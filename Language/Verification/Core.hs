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

module Language.Verification.Core where

import           Control.Exception
import           Data.Typeable            ((:~:) (..), Typeable)

import           Control.Lens             hiding ((.>))
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State

import           Data.Map                 (Map)
import           Data.SBV                 hiding (OrdSymbolic (..), ( # ))

import           Language.Expression
import           Language.Expression.Prop (LogicOp, Prop)

--------------------------------------------------------------------------------
--  Variables
--------------------------------------------------------------------------------

class (Typeable v, Ord (VarKey v), Show (VarKey v), Typeable (VarKey v)) => VerifiableVar v where
  type VarKey v
  type VarSym v :: * -> *
  type VarEnv v :: *

  symForVar :: v a -> VarEnv v -> Symbolic (VarSym v a)
  varKey :: v a -> VarKey v

  eqVarTypes :: v a -> v b -> Maybe (a :~: b)

  castVarSym :: v a -> VarSym v b -> Maybe (VarSym v a)

--------------------------------------------------------------------------------
--  Verifier Monad
--------------------------------------------------------------------------------

data VerifierError v
  = VEMismatchedSymbolType (VarKey v)
  -- ^ The same variable was used for two different symbol types
  | VESbvException String String
  -- ^ When running a query, SBV threw an exception

deriving instance Show (VarKey v) => Show (VerifierError v)
deriving instance Typeable (VarKey v) => Typeable (VerifierError v)

instance (Typeable v, l ~ VarKey v, Show l, Typeable l) =>
  Exception (VerifierError v) where

  displayException = \case
    VEMismatchedSymbolType l ->
      "variable " ++ show l ++ " was used at two different types"

    VESbvException message (_ {- location -}) ->
      "exception from SBV:\n" ++ message

newtype Verifier v a =
  Verifier
  { getVerifier :: ReaderT SMTConfig (ExceptT (VerifierError v) IO) a
  }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadIO
           , MonadReader SMTConfig
           , MonadError (VerifierError v)
           )

runVerifierWith
  :: (VerifiableVar v)
  => SMTConfig
  -> Verifier v a
  -> IO (Either (VerifierError v) a)
runVerifierWith config (Verifier action) = runExceptT (runReaderT action config)

runVerifier
  :: VerifiableVar v
  => Verifier v a -> IO (Either (VerifierError v) a)
runVerifier = runVerifierWith defaultSMTCfg

--------------------------------------------------------------------------------
--  Query Monad
--------------------------------------------------------------------------------

data SomeSym v where
  SomeSym :: VarSym v a -> SomeSym v

type QueryState v = Map (VarKey v) (SomeSym v)

newtype Query v a =
  Query
  { getQuery :: ReaderT (VarEnv v) (
      StateT (QueryState v) Symbolic) a
  }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadIO
           )

query :: (VerifiableVar v) => Query v SBool -> VarEnv v -> Verifier v Bool
query (Query action) env = do
  cfg <- ask
  let predicate = evalStateT (runReaderT action env) mempty
      smtResult =
        (Right <$> isTheoremWith cfg predicate) `catches`
        [ Handler (\ex -> return (Left ex))
        , Handler (\(ErrorCallWithLocation message location) ->
                     return (Left (VESbvException message location)))
        ]

  liftIO smtResult >>= either throwError return

--------------------------------------------------------------------------------
--  Query actions
--------------------------------------------------------------------------------

evalProp
  :: ( HMonad expr
     , HTraversable expr
     , VerifiableVar v
     , Exception (VerifierError v)
     , HFoldableAt k expr
     , HFoldableAt k LogicOp
     , Monad m
     )
  => (forall a. Query v a -> m a)
  -> (forall a. VarSym v a -> m (k a))
  -> Prop (expr v) b
  -> m (k b)
evalProp liftQuery liftVar = hfoldTraverseAt (hfoldTraverseAt (liftVar <=< liftQuery . symbolVar))

evalProp'
  :: ( HMonad expr
     , HTraversable expr
     , VerifiableVar v
     , Exception (VerifierError v)
     , HFoldableAt SBV expr
     , VarSym v ~ SBV
     )
  => Prop (expr v) b
  -> Query v (SBV b)
evalProp' = evalProp id pure

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

-- | If the two variables match in both type and name, return the given
-- expression. Otherwise, return an expression just containing this variable.
--
-- This is substitution into an expression, where the old expression is just a
-- variable.
subVar
  :: (HPointed expr, VerifiableVar v, Eq (VarKey v))
  => expr v a
  -> v a
  -> v b
  -> expr v b
subVar newExpr targetVar thisVar =
  let targetName = varKey targetVar
      thisName = varKey thisVar
  in case eqVarTypes thisVar targetVar of
       Just Refl | thisName == targetName -> newExpr
       _         -> hpure thisVar

--------------------------------------------------------------------------------
--  Internal Functions
--------------------------------------------------------------------------------

liftSymbolic :: Symbolic a -> Query v a
liftSymbolic = Query . lift . lift

throwQuery :: (Exception (VerifierError v)) => VerifierError v -> Query v a
throwQuery = liftIO . throwIO

symbolVar :: (VerifiableVar v, Exception (VerifierError v)) => v a -> Query v (VarSym v a)
symbolVar theVar = do
  let varLoc = varKey theVar
  storedSymbol <- Query $ use (at varLoc)

  case storedSymbol of
    Just (SomeSym x) -> case castVarSym theVar x of
      Just y  -> return y
      Nothing -> throwQuery (VEMismatchedSymbolType varLoc)
    Nothing -> do
      newSymbol <- liftSymbolic . symForVar theVar =<< Query ask
      Query $ at varLoc .= Just (SomeSym newSymbol)
      return newSymbol
