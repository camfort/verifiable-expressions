{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

module Language.Verification.Core where

import           Data.Data

import           Control.Lens            hiding ((.>))
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State

import           Data.Map                (Map)
import           Data.SBV                hiding (OrdSymbolic (..), ( # ))

import           Language.Expression
import           Language.Expression.SBV

--------------------------------------------------------------------------------
--  Verifiable Types
--------------------------------------------------------------------------------

data VerifierSymbol f
  = VSInteger (f Integer)
  | VSWord8 (f Word8)
  | VSWord16 (f Word16)
  | VSWord32 (f Word32)
  | VSWord64 (f Word64)
  | VSInt8 (f Int8)
  | VSInt16 (f Int16)
  | VSInt32 (f Int32)
  | VSInt64 (f Int64)
  | VSBool (f Bool)
  | VSReal (f AlgReal)
  | VSFloat (f Float)
  | VSDouble (f Double)

makePrisms ''VerifierSymbol

class Typeable a => Verifiable a where
  _Symbol :: Prism' (VerifierSymbol f) (f a)

instance Verifiable Integer where _Symbol = _VSInteger
instance Verifiable Word8 where _Symbol = _VSWord8
instance Verifiable Word16 where _Symbol = _VSWord16
instance Verifiable Word32 where _Symbol = _VSWord32
instance Verifiable Word64 where _Symbol = _VSWord64
instance Verifiable Int8 where _Symbol = _VSInt8
instance Verifiable Int16 where _Symbol = _VSInt16
instance Verifiable Int32 where _Symbol = _VSInt32
instance Verifiable Int64 where _Symbol = _VSInt64
instance Verifiable Bool where _Symbol = _VSBool
instance Verifiable Float where _Symbol = _VSFloat
instance Verifiable Double where _Symbol = _VSDouble
instance Verifiable AlgReal where _Symbol = _VSReal

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
  | VEEval EvalError
  -- ^ The same variable was used for two different symbol types
  deriving (Show, Eq, Ord, Data, Typeable)

newtype Verifier l expr a =
  Verifier
  { getVerifier ::
      ReaderT SMTConfig (
        ExceptT (VerifierError l expr)
          IO) a
  }
  deriving (Functor, Applicative, Monad, MonadIO,
            MonadReader SMTConfig, MonadError (VerifierError l expr))

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
  { _varSymbols :: Map l (VerifierSymbol SBV)
  }

makeLenses ''QueryState

qs0 :: Ord l => QueryState l expr
qs0 = QueryState mempty

newtype Query l expr a =
  Query
  { getQuery ::
      StateT (QueryState l expr) (
        ExceptT (VerifierError l expr)
          Symbolic) a
  }
  deriving (Functor, Applicative, Monad,
            MonadState (QueryState l expr),
            MonadError (VerifierError l expr))

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
  :: (Substitutive expr, Eq l)
  => expr (Var l) a
  -> Var l a
  -> Var l b
  -> expr (Var l) b
subVar newExpr (Var targetName) thisVar@(Var thisName) =
  case gcast newExpr of
    Just newExpr' | thisName == targetName -> newExpr'
    _ -> pureVar thisVar

--------------------------------------------------------------------------------
--  Internal Functions
--------------------------------------------------------------------------------

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
