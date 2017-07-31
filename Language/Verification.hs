{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving#-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}


-- TODO: Stop nesting 'Symbolic' contexts!
-- https://github.com/LeventErkok/sbv/issues/71

module Language.Verification
  (
  -- * The verification monad
    Verifier
  , runVerifier
  , runVerifierWith
  , VerifierError(..)

  -- * The query monad
  , Query
  , query

  -- * Verifiable types and variables
  , VerifierSymbol
  , Verifiable(..)
  , Location(..)
  , Var(..)

  -- * Verifier actions
  , checkProp

  -- * Miscellaneous combinators
  , subVar
  ) where

import           Data.Data

import           Control.Lens                               hiding ((.>))
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Reader

import           Data.Map                                   (Map)
import           Data.SBV                                   hiding (( # ), OrdSymbolic(..))
import qualified Data.SBV.Control as S

import           Language.Verification.Expression
import           Language.Verification.Expression.Operators

--------------------------------------------------------------------------------
--  Verifiable Types
--------------------------------------------------------------------------------

data VerifierSymbol f
  = VSInteger (f Integer)
  | VSBool (f Bool)
  | VSReal (f AlgReal)

makePrisms ''VerifierSymbol

class Typeable a => Verifiable a where
  _Symbol :: Prism' (VerifierSymbol f) (f a)

instance Verifiable Integer where
  _Symbol = _VSInteger

instance Verifiable Bool where
  _Symbol = _VSBool

instance Verifiable AlgReal where
  _Symbol = _VSReal

--------------------------------------------------------------------------------
--  Variables
--------------------------------------------------------------------------------

class (Ord l) => Location l where
  locationName :: l -> String

instance Location String where locationName = id

-- | A variable with locations in @l@ representing values of type @a@.
data Var l a where
  Var :: (SymWord a, Verifiable a) => l -> Var l a

--------------------------------------------------------------------------------
--  Verifier Monad
--------------------------------------------------------------------------------

data VerifierError l (expr :: (* -> *) -> * -> *)
  = VEMismatchedSymbolType l
  -- ^ The same variable was used for two different symbol types
  deriving (Show, Eq, Ord, Data, Typeable)

newtype Verifier l expr a =
  Verifier
  { getVerifier ::
      ReaderT SMTConfig (
        ExceptT (VerifierError l expr)
          IO) a
  }
  deriving (Functor, Applicative, Monad, MonadIO, MonadReader SMTConfig, MonadError (VerifierError l expr))

runVerifierWith
  :: (Location l)
  => SMTConfig
  -> Verifier l expr a
  -> IO (Either (VerifierError l expr) a)
runVerifierWith config (Verifier action) = runExceptT (runReaderT action config)

runVerifier :: Location l => Verifier l expr a -> IO (Either (VerifierError l expr) a)
runVerifier = runVerifierWith defaultSMTCfg

--------------------------------------------------------------------------------
--  Query Monad
--------------------------------------------------------------------------------

data QueryState l (expr :: (* -> *) -> * -> *) =
  QueryState
  { _varSymbols    :: Map l (VerifierSymbol SBV)
  }

makeLenses ''QueryState

qs0 :: Ord l => QueryState l expr
qs0 = QueryState mempty

newtype Query l expr a =
  Query
  { getQuery :: StateT (QueryState l expr) (ExceptT (VerifierError l expr) Symbolic) a
  }
  deriving (Functor, Applicative, Monad, MonadState (QueryState l expr), MonadError (VerifierError l expr))

query :: (Location l) => Query l expr a -> Verifier l expr a
query (Query action) =
  do cfg <- ask
     r <- liftIO (runSMTWith cfg (runExceptT (evalStateT action qs0)))
     either throwError return r

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

-- | If the two variables match in both type and name, return the given
-- expression. Otherwise, return an expression just containing this variable.
--
-- This is substitution into an expression, where the old expression is just a
-- variable.
subVar
  :: forall expr a b l. (Substitutive expr, Eq l)
  => expr (Var l) a
  -> Var l a
  -> Var l b
  -> expr (Var l) b
subVar newExpr (Var targetName) thisVar@(Var thisName) =
  case eqT :: Maybe (a :~: b) of
    Just Refl | thisName == targetName -> newExpr
    _ -> pureVar thisVar

--------------------------------------------------------------------------------
--  Query actions
--------------------------------------------------------------------------------

checkProp
  :: (Substitutive expr, HoistOp SBV expr, Location l)
  => PropOn (expr (Var l)) Bool
  -> Query l expr Bool
checkProp prop = do
  symbolicProp <- propToSBV prop
  -- cfg <- Verifier ask
  -- liftIO (isTheoremWith cfg symbolicProp)
  liftSymbolic . S.query $ do
    constrain (bnot symbolicProp)
    cs <- S.checkSat
    case cs of
      S.Unsat -> return True
      _ -> return False

--------------------------------------------------------------------------------
--  Internal Functions
--------------------------------------------------------------------------------

propToSBV
  :: (Substitutive expr, HoistOp SBV expr, Location l)
  => PropOn (expr (Var l)) Bool
  -> Query l expr SBool
propToSBV prop = do
  propWithSymbols <- htraverseOp (htraverseOp symbolVar) prop

  let evalExpr' = runIdentity . evalOp . hoistOp pure
      result = evalExpr' (hmapOp evalExpr' propWithSymbols)

  return result

liftSymbolic :: Symbolic a -> Query l v a
liftSymbolic = Query . lift . lift

symbolVar :: Location l => Var l a -> Query l expr (SBV a)
symbolVar (Var varLoc) = do
  storedSymbol <- Query $ use (varSymbols . at varLoc)

  case storedSymbol of
    Just s -> maybe (throwError (VEMismatchedSymbolType varLoc))
              return
              (s ^? _Symbol)
    Nothing -> do
      newSymbol <- liftSymbolic (symbolic (locationName varLoc))
      varSymbols . at varLoc .= Just (_Symbol # newSymbol)
      return newSymbol
