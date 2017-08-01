{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}

{-|

This module provides the ability to evaluate expressions to 'SBV' values which
can be sent off to an SMT solver to have properties proved about them.

-}
module Language.Expression.SBV
  (
  -- * The evaluation monad
    EvalError(..)
  , EvalT
  , runEvalT
  , runDefaultEvalT
  -- * Evaluation context
  , EvalContext(..)
  , numDicts
  , eqDicts
  , ordDicts
  , booleanDicts
  , defaultEvalContext
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

-- | The standard evaluation context type (which will need to be extended if you
-- use operations other than the standard ones).
data EvalContext =
  EvalContext
  { _numDicts     :: Dictmap NumDict
  , _eqDicts      :: Dictmap2 EqDict
  , _ordDicts     :: Dictmap2 OrdDict
  , _booleanDicts :: Dictmap BooleanDict
  }

makeLenses ''EvalContext

-- | A default evaluation context which contains dictionaries for all of the
-- built-in 'SBV' types.
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

-- | An error that might occur while evaluating an expression in the 'EvalT'
-- transformer.
data EvalError
  = MissingInstance String [TypeRep]
  -- ^ The dictionary was missing an instance for these types.
  deriving (Show, Eq, Ord, Data, Typeable)

-- | The dictionary was missing an instance for this type.
missingInstance :: (MonadError EvalError m) => String -> TypeRep -> m a
missingInstance msg t = throwError $ MissingInstance msg [t]

-- | The dictionary was missing an instance for these types.
missingInstance2 :: (MonadError EvalError m) => String -> TypeRep -> TypeRep -> m a
missingInstance2 msg t1 t2 = throwError $ MissingInstance msg [t1, t2]


{-|

Evaluation monad transformer. Can be used to evaluate operators (and hence expressions) to 'SBV' values.

Notice that 'evalOp' can be specialized to:

@
type EvalVar m v b = v b -> 'EvalT' 'EvalContext' m ('SBV' b)
'evalOp' :: (Monad m) => (forall b. EvalVar m v b) -> 'Expr'' 'StandardOps' v a -> 'EvalT' 'EvalContext' m ('SBV' a)
@

I.e. given a way to evaluate variables to 'SBV' values in @'EvalT' 'EvalContext'
m@ (which can be lifted from the underlying monad @m@), we can evaluate the
whole expression to an 'SBV' value.

To extend expressions with more operators, i.e. @'Expr\'' (MyOp : 'StandardOps')
v a@, add instances for @'EvalOp' ('EvalT' r m)@ for some @r@.

-}
newtype EvalT r m a = EvalT { getEvalT :: ExceptT EvalError (ReaderT r m) a }
  deriving (Functor, Applicative, Monad, MonadError EvalError, MonadReader r)

instance MonadTrans (EvalT r) where
  lift = EvalT . lift . lift

-- | Run the evaluation with a given context. Results in an error value if the
-- necessary dictionaries did not exist.
runEvalT :: EvalT r m a -> r -> m (Either EvalError a)
runEvalT = runReaderT . runExceptT . getEvalT

-- | Run the evaluation with the default context which includes dictionaries for
-- all of the built-in 'SBV' types. If you have defined your own 'SBV' types you
-- will need to add them to the dictionaries and use 'runEvalT'.
runDefaultEvalT :: EvalT EvalContext m a -> m (Either EvalError a)
runDefaultEvalT action = runEvalT action defaultEvalContext

--------------------------------------------------------------------------------
--  Instances
--------------------------------------------------------------------------------

-- | Expressions containing boolean operations may be evaluated to symbolic
-- 'SBV' values.
instance (Monad m, HasDicts BooleanDict r) => EvalOp (EvalT r m) SBV BoolOp where
  evalOp f = \case
    OpNot x -> unaryOpFromDict (missingInstance "Boolean") dictNot (f x)
    OpAnd x y -> binaryOpFromDict (missingInstance "Boolean") dictAnd (f x) (f y)
    OpOr x y -> binaryOpFromDict (missingInstance "Boolean") dictOr (f x) (f y)
    OpImpl x y -> binaryOpFromDict (missingInstance "Boolean") dictImpl (f x) (f y)
    OpEquiv x y -> binaryOpFromDict (missingInstance "Boolean") dictEquiv (f x) (f y)


-- | Expressions containing numeric operations may be evaluated to symbolic
-- 'SBV' values.
instance (Monad m, HasDicts NumDict r) => EvalOp (EvalT r m) SBV NumOp where
  evalOp f = \case
    OpAdd x y -> binaryOpFromDict (missingInstance "Num") dictAdd (f x) (f y)
    OpMul x y -> binaryOpFromDict (missingInstance "Num") dictMul (f x) (f y)
    OpSub x y -> binaryOpFromDict (missingInstance "Num") dictSub (f x) (f y)


-- | Expressions containing equality operations may be evaluated to symbolic
-- 'SBV' values.
instance (Monad m, HasDicts2 EqDict r) => EvalOp (EvalT r m) SBV EqOp where
  evalOp f = \case
    OpEq x y -> binaryOpFromDict2 (missingInstance2 "Eq") dictEq (f x) (f y)


-- | Expressions containing ordering operations may be evaluated to symbolic
-- 'SBV' values.
instance (Monad m, HasDicts2 OrdDict r) => EvalOp (EvalT r m) SBV OrdOp where
  evalOp f = \case
    OpLT x y -> binaryOpFromDict2 (missingInstance2 "Ord") dictLt (f x) (f y)
    OpLE x y -> binaryOpFromDict2 (missingInstance2 "Ord") dictLe (f x) (f y)
    OpGT x y -> binaryOpFromDict2 (missingInstance2 "Ord") dictGt (f x) (f y)
    OpGE x y -> binaryOpFromDict2 (missingInstance2 "Ord") dictGe (f x) (f y)

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------


-- | In a monad where we have access to dictionaries of a particular type
-- @dict@, look for @dict a@ which provides operations for the given type @a@.
-- If this dictionary exists, extract the desired unary operation and lift it
-- into the monad. Otherwise, report that it doesn't exist with the given error
-- reporting function.
--
-- This is useful for providing operator evaluation instances.
unaryOpFromDict
  :: forall dict r m a b.
     (HasDicts dict r,
      MonadReader r m,
      Typeable a,
      Typeable b)
  => (forall x. TypeRep -> m x)
  -- ^ Given a representation of the type @a@, create an error that reports that
  -- no instance could be found.
  -> Lens' (dict b) (a -> b)
  -- ^ A lens which extracts the desired operation from the dictionary.
  -> m a -> m b
unaryOpFromDict err l x =
  do mOp <- preview (dictFor Proxy . l)
     case mOp of
       Just o -> o <$> x
       Nothing -> err (typeRep (Proxy :: Proxy a))

-- | In a monad where we have access to dictionaries of a particular type
-- @dict@, look for @dict a@ which provides operations for the given type @a@.
-- If this dictionary exists, extract the desired binary operation and lift it
-- into the monad. Otherwise, report that it doesn't exist with the given error
-- reporting function.
--
-- This is useful for providing operator evaluation instances.
binaryOpFromDict
  :: forall dict r m a.
     (HasDicts dict r,
      MonadReader r m,
      Typeable a)
  => (forall x. TypeRep -> m x)
  -- ^ Given a representation of the type @a@, create an error that reports that
  -- no instance could be found.
  -> Lens' (dict a) (a -> a -> a)
  -- ^ A lens which extracts the desired operation from the dictionary.
  -> m a -> m a -> m a
binaryOpFromDict err l x y =
  do mOp <- preview (dictFor Proxy . l)
     case mOp of
       Just o -> o <$> x <*> y
       Nothing -> err (typeRep (Proxy :: Proxy a))


-- | In a monad where we have access to dictionaries of a particular type
-- @dict@, look for @dict a b@ which provides operations for the given types @a@
-- and @b@. If this dictionary exists, extract the desired binary operation and
-- lift it into the monad. Otherwise, report that it doesn't exist with the
-- given error reporting function.
--
-- This is useful for providing operator evaluation instances.
binaryOpFromDict2
  :: forall dict r m a b.
     (HasDicts2 dict r,
      MonadReader r m,
      Typeable a,
      Typeable b)
  => (forall x. TypeRep -> TypeRep -> m x)
  -- ^ Given a representation of the type @a@, create an error that reports that
  -- no instance could be found.
  -> Lens' (dict b a) (a -> a -> b)
  -- ^ A lens which extracts the desired operation from the dictionary.
  -> m a -> m a -> m b
binaryOpFromDict2 err l x y =
  do mOp <- preview (dict2For Proxy Proxy . l)
     case mOp of
       Just o -> o <$> x <*> y
       Nothing -> err (typeRep (Proxy :: Proxy a)) (typeRep (Proxy :: Proxy b))
