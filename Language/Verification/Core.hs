{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

module Language.Verification.Core where

import           Control.Exception
import           Data.Typeable                    ((:~:) (..), Typeable)

import           Control.Lens                     hiding ((.>))
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State

import           Data.Map                         (Map)
import           Data.SBV                         hiding (OrdSymbolic (..),
                                                   ( # ))
import qualified Data.SBV.Control                 as S

import           Language.Expression
import           Language.Expression.DSL          (PropOver)
import           Language.Expression.Ops.Standard (LogicOp)

--------------------------------------------------------------------------------
--  Variables
--------------------------------------------------------------------------------

class (Ord (VarKey v)) => VerifiableVar v where
  type VarKey v
  type VarSym v :: * -> *

  symForVar :: v a -> Symbolic (VarSym v a)
  varKey :: v a -> VarKey v

  eqVarTypes :: v a -> v b -> Maybe (a :~: b)

  castVarSym :: v a -> VarSym v b -> Maybe (VarSym v a)

--------------------------------------------------------------------------------
--  Verifier Monad
--------------------------------------------------------------------------------

data VerifierError v (expr :: (* -> *) -> * -> *)
  = VEMismatchedSymbolType (VarKey v)
  -- ^ The same variable was used for two different symbol types

deriving instance Show (VarKey v) => Show (VerifierError v expr)
deriving instance Eq (VarKey v) => Eq (VerifierError v expr)
deriving instance Ord (VarKey v) => Ord (VerifierError v expr)
deriving instance Typeable (VarKey v) => Typeable (VerifierError v expr)

instance (Typeable v, l ~ VarKey v, Show l, Typeable l, Typeable expr) =>
  Exception (VerifierError v expr) where

  displayException = \case
    VEMismatchedSymbolType l ->
      "variable " ++ show l ++ " was used at two different types"

newtype Verifier v expr a =
  Verifier
  { getVerifier ::
      ReaderT SMTConfig (
        ExceptT (VerifierError v expr)
          IO) a
  }
  deriving (Functor, Applicative, Monad, MonadIO,
            MonadReader SMTConfig, MonadError (VerifierError v expr))

runVerifierWith
  :: (VerifiableVar v)
  => SMTConfig
  -> Verifier v expr a
  -> IO (Either (VerifierError v expr) a)
runVerifierWith config (Verifier action) = runExceptT (runReaderT action config)

runVerifier
  :: VerifiableVar v
  => Verifier v expr a -> IO (Either (VerifierError v expr) a)
runVerifier = runVerifierWith defaultSMTCfg

--------------------------------------------------------------------------------
--  Query Monad
--------------------------------------------------------------------------------

data SomeSym v where
  SomeSym :: VarSym v a -> SomeSym v

data QueryState v (expr :: (* -> *) -> * -> *) =
  QueryState
  { _varSymbols :: Map (VarKey v) (SomeSym v)
  }

makeLenses ''QueryState

qs0 :: Ord (VarKey v) => QueryState v expr
qs0 = QueryState mempty

newtype Query v expr a =
  Query
  { getQuery ::
      StateT (QueryState v expr) (
        ExceptT (VerifierError v expr)
          Symbolic) a
  }
  deriving (Functor, Applicative, Monad,
            MonadState (QueryState v expr),
            MonadError (VerifierError v expr))

query :: (VerifiableVar v) => Query v expr a -> Verifier v expr a
query (Query action) =
  do cfg <- ask
     r <- liftIO (runSMTWith cfg (runExceptT (evalStateT action qs0)))
     either throwError return r

--------------------------------------------------------------------------------
--  Query actions
--------------------------------------------------------------------------------

-- | Check a proposition by evaluating it symbolically (with the default
-- standard environment) and sending it to the SMT solver.
checkProp
  :: (Substitutive expr, VerifiableVar v,
      EvalOp (Query v expr) SBV expr,
      VarSym v ~ SBV)
  => PropOver (expr v) Bool
  -> Query v expr Bool
checkProp = checkPropWith id id

checkPropWith
  :: (Substitutive expr, VerifiableVar v,
      EvalOp (Query v expr) k expr,
      EvalOp (Query v expr) k LogicOp)
  => (k Bool -> SBV Bool)
  -- ^ Run the evaluation result in SBV
  -> (forall a. VarSym v a -> k a)
  -- ^ Lift symbolic variables into the result type
  -> PropOver (expr v) Bool
  -> Query v expr Bool
checkPropWith runTarget liftVar prop = do
  symbolicProp <- runTarget <$> evalOp (evalOp (fmap liftVar . symbolVar)) prop
  liftSymbolic . S.query $ do
    constrain (bnot symbolicProp)
    cs <- S.checkSat
    case cs of
      S.Unsat -> return True
      _       -> return False

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

-- | If the two variables match in both type and name, return the given
-- expression. Otherwise, return an expression just containing this variable.
--
-- This is substitution into an expression, where the old expression is just a
-- variable.
subVar
  :: (Substitutive expr, VerifiableVar v, Eq (VarKey v))
  => expr v a
  -> v a
  -> v b
  -> expr v b
subVar newExpr targetVar thisVar =
  let targetName = varKey targetVar
      thisName = varKey thisVar
  in case eqVarTypes thisVar targetVar of
       Just Refl | thisName == targetName -> newExpr
       _         -> pureVar thisVar

--------------------------------------------------------------------------------
--  Internal Functions
--------------------------------------------------------------------------------

liftSymbolic :: Symbolic a -> Query l v a
liftSymbolic = Query . lift . lift

symbolVar :: VerifiableVar v => v a -> Query v expr (VarSym v a)
symbolVar theVar = do
  let varLoc = varKey theVar
  storedSymbol <- Query $ use (varSymbols . at varLoc)

  case storedSymbol of
    Just (SomeSym x) -> case castVarSym theVar x of
      Just y  -> return y
      Nothing -> throwError (VEMismatchedSymbolType varLoc)
    Nothing -> do
      newSymbol <- liftSymbolic (symForVar theVar)
      varSymbols . at varLoc .= Just (SomeSym newSymbol)
      return newSymbol
