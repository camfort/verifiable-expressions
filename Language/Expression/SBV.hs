{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}

module Language.Expression.SBV
  (
  -- * Evaluation context
    EvalContext(..)
  , numDicts
  , eqDicts
  , ordDicts
  , booleanDicts
  , defaultEvalContext
  -- * The evaluation monad
  , EvalError(..)
  , EvalT
  , runEvalT
  -- * Combinators for writing 'EvalOp' instances
  , unaryOpFromDict
  , binaryOpFromDict
  , binaryOpFromDict2
  ) where

import           Data.Data                          (Data)
import           Data.Typeable                      (Proxy (..), TypeRep,
                                                     Typeable, typeRep)

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader

import           Data.SBV                           (SBV)

import           Language.Expression
import           Language.Expression.Dict
import           Language.Expression.Dict.Instances
import           Language.Expression.Operators

--------------------------------------------------------------------------------
--  Contexts
--------------------------------------------------------------------------------

data EvalContext =
  EvalContext
  { _numDicts     :: Dictmap NumDict
  , _eqDicts      :: Dictmap2 EqDict
  , _ordDicts     :: Dictmap2 OrdDict
  , _booleanDicts :: Dictmap BooleanDict
  }

makeLenses ''EvalContext

defaultEvalContext :: EvalContext
defaultEvalContext =
  EvalContext
  { _numDicts = standardNumInstances
  , _eqDicts = standardEqInstances
  , _ordDicts = standardOrdInstances
  , _booleanDicts = standardBooleanInstances
  }

instance HasDicts NumDict EvalContext where
  dicts = numDicts

instance HasDicts2 EqDict EvalContext where
  dicts2 = eqDicts

instance HasDicts2 OrdDict EvalContext where
  dicts2 = ordDicts

instance HasDicts BooleanDict EvalContext where
  dicts = booleanDicts

--------------------------------------------------------------------------------
--  Evaluation monad
--------------------------------------------------------------------------------

data EvalError
  = MissingBooleanInstance TypeRep
  | MissingNumInstance TypeRep
  | MissingOrdInstance TypeRep
  | MissingEqInstance TypeRep
  deriving (Show, Eq, Ord, Data, Typeable)


newtype EvalT r m a = EvalT { getEvalT :: ExceptT EvalError (ReaderT r m) a }
  deriving (Functor, Applicative, Monad, MonadError EvalError, MonadReader r)

instance MonadTrans (EvalT r) where
  lift = EvalT . lift . lift

runEvalT :: EvalT r m a -> r -> m (Either EvalError a)
runEvalT = runReaderT . runExceptT . getEvalT

--------------------------------------------------------------------------------
--  Instances
--------------------------------------------------------------------------------

instance (Monad m, HasDicts BooleanDict r) => EvalOp (EvalT r m) SBV BoolOp where
  evalOp f = \case
    OpNot x -> unaryOpFromDict MissingBooleanInstance dictNot (f x)
    OpAnd x y -> binaryOpFromDict MissingBooleanInstance dictAnd (f x) (f y)
    OpOr x y -> binaryOpFromDict MissingBooleanInstance dictOr (f x) (f y)
    OpImpl x y -> binaryOpFromDict MissingBooleanInstance dictImpl (f x) (f y)
    OpEquiv x y -> binaryOpFromDict MissingBooleanInstance dictEquiv (f x) (f y)


instance (Monad m, HasDicts NumDict r) => EvalOp (EvalT r m) SBV NumOp where
  evalOp f = \case
    OpAdd x y -> binaryOpFromDict MissingNumInstance dictAdd (f x) (f y)
    OpMul x y -> binaryOpFromDict MissingNumInstance dictMul (f x) (f y)
    OpSub x y -> binaryOpFromDict MissingNumInstance dictSub (f x) (f y)


instance (Monad m, HasDicts2 EqDict r) => EvalOp (EvalT r m) SBV EqOp where
  evalOp f = \case
    OpEq x y -> binaryOpFromDict2 MissingEqInstance dictEq (f x) (f y)


instance (Monad m, HasDicts2 OrdDict r) => EvalOp (EvalT r m) SBV OrdOp where
  evalOp f = \case
    OpLT x y -> binaryOpFromDict2 MissingOrdInstance dictLt (f x) (f y)
    OpLE x y -> binaryOpFromDict2 MissingOrdInstance dictLe (f x) (f y)
    OpGT x y -> binaryOpFromDict2 MissingOrdInstance dictGt (f x) (f y)
    OpGE x y -> binaryOpFromDict2 MissingOrdInstance dictGe (f x) (f y)

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

unaryOpFromDict
  :: forall dict r e m a b.
     (HasDicts dict r,
      MonadError e m,
      MonadReader r m,
      Typeable a,
      Typeable b)
  => (TypeRep -> e) -> Lens' (dict b) (a -> b) -> m a -> m b
unaryOpFromDict err l x =
  do mOp <- preview (dictFor Proxy . l)
     case mOp of
       Just o -> o <$> x
       Nothing -> throwError (err (typeRep (Proxy :: Proxy a)))


binaryOpFromDict
  :: forall dict r e m a.
     (HasDicts dict r,
      MonadError e m,
      MonadReader r m,
      Typeable a)
  => (TypeRep -> e)
  -> Lens' (dict a) (a -> a -> a)
  -> m a -> m a -> m a
binaryOpFromDict err l x y =
  do mOp <- preview (dictFor Proxy . l)
     case mOp of
       Just o -> o <$> x <*> y
       Nothing -> throwError (err (typeRep (Proxy :: Proxy a)))


binaryOpFromDict2
  :: forall dict r e m a b.
     (HasDicts2 dict r,
      MonadError e m,
      MonadReader r m,
      Typeable a,
      Typeable b)
  => (TypeRep -> e)
  -> Lens' (dict b a) (a -> a -> b)
  -> m a -> m a -> m b
binaryOpFromDict2 err l x y =
  do mOp <- preview (dict2For Proxy Proxy . l)
     case mOp of
       Just o -> o <$> x <*> y
       Nothing -> throwError (err (typeRep (Proxy :: Proxy a)))
