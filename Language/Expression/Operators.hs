{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeOperators              #-}

{-|

A collection of standard operator types which may be used to form expressions.

-}
module Language.Expression.Operators
  (
  -- * Standard operators
    LogicOp(..)
  , BoolOp(..)
  , EqOp(..)
  , OrdOp(..)
  , LitOp(..)
  , NumOp(..)
  , CoerceOp(..)

  -- * Standard Operators
  , StandardOps

  -- * Evaluating purely
  , PureEval(..)

  -- * Expression and operator type classes
  , module Expression

  -- * Classes used to constrain operator types
  , module Classes
  ) where

import           Control.Applicative         (liftA2)
import           Data.Functor.Classes
import           Data.Functor.Compose
import           Data.Typeable               ((:~:) (..), Typeable, eqT)

import           Data.SBV                    (SBV)

import           Language.Expression         as Expression
import           Language.Expression.Classes as Classes

--------------------------------------------------------------------------------
--  Operators
--------------------------------------------------------------------------------

{-| A newtype wrapper to evaluate operators in a pure context.

e.g.

@
getPureEval . evalOp' PureEval :: Expr' StandardOps Maybe a -> Maybe a
@

Notice this expression contains variables in 'Maybe', which actually means that
"variables" have been substituted for literal values that may or may not exist.

-}
newtype PureEval f a = PureEval { getPureEval :: f a }
  deriving (Functor, Applicative, Monad)

-- | Boolean operations.
data BoolOp t a where
  OpNot :: SymBool b => t b -> BoolOp t b
  OpAnd :: SymBool b => t b -> t b -> BoolOp t b
  OpOr :: SymBool b => t b -> t b -> BoolOp t b

instance Operator BoolOp where
  htraverseOp f = \case
    OpNot x -> OpNot <$> f x
    OpAnd x y -> OpAnd <$> f x <*> f y
    OpOr x y -> OpOr <$> f x <*> f y

instance (Applicative f, Applicative g) => EvalOp f (PureEval g) BoolOp where
  evalOp f = \case
    OpNot x -> fmap symNot <$> f x
    OpAnd x y -> liftA2' f symAnd x y
    OpOr x y -> liftA2' f symOr x y

instance HigherEq BoolOp where
  liftHigherEq le _ (OpNot x) (OpNot y) = le svEq x y
  liftHigherEq le _ (OpAnd x1 x2) (OpAnd y1 y2) = le svEq x1 y1 && le svEq x2 y2
  liftHigherEq le _ (OpOr x1 x2) (OpOr y1 y2) = le svEq x1 y1 && le svEq x2 y2
  liftHigherEq _ _ _ _ = False

instance (Eq1 t) => Eq1 (BoolOp t) where liftEq = liftEqFromHigher

instance (Eq a, Eq1 t) => Eq (BoolOp t a) where (==) = eq1


-- | Logical operations
data LogicOp t a where
  LogLit :: SymBool b => Bool -> LogicOp t b
  LogNot :: SymBool b => t b -> LogicOp t b
  LogAnd :: SymBool b => t b -> t b -> LogicOp t b
  LogOr :: SymBool b => t b -> t b -> LogicOp t b
  LogImpl :: SymBool b => t b -> t b -> LogicOp t b
  LogEquiv :: SymBool b => t b -> t b -> LogicOp t b

instance Operator LogicOp where
  htraverseOp f = \case
    LogLit b -> pure $ LogLit b
    LogNot x -> LogNot <$> f x
    LogAnd x y -> LogAnd <$> f x <*> f y
    LogOr x y -> LogOr <$> f x <*> f y
    LogImpl x y -> LogImpl <$> f x <*> f y
    LogEquiv x y -> LogEquiv <$> f x <*> f y

instance (Applicative f, Applicative g) => EvalOp f (PureEval g) LogicOp where
  evalOp f = \case
    LogLit b -> pure (PureEval (pure (symFromBool b)))
    LogNot x -> fmap symNot <$> f x
    LogAnd x y -> liftA2' f symAnd x y
    LogOr x y -> liftA2' f symOr x y
    LogImpl x y -> liftA2' f symImpl x y
    LogEquiv x y -> liftA2' f symEquiv x y

instance HigherEq LogicOp where
  liftHigherEq _ _ (LogLit x) (LogLit y) = x == y
  liftHigherEq le _ (LogNot x) (LogNot y) = le svEq x y
  liftHigherEq le _ (LogAnd x1 x2) (LogAnd y1 y2) = le svEq x1 y1 && le svEq x2 y2
  liftHigherEq le _ (LogOr x1 x2) (LogOr y1 y2) = le svEq x1 y1 && le svEq x2 y2
  liftHigherEq le _ (LogImpl x1 x2) (LogImpl y1 y2) = le svEq x1 y1 && le svEq x2 y2
  liftHigherEq le _ (LogEquiv x1 x2) (LogEquiv y1 y2) = le svEq x1 y1 && le svEq x2 y2
  liftHigherEq _ _ _ _ = False

instance (Eq1 t) => Eq1 (LogicOp t) where liftEq = liftEqFromHigher

instance (Eq a, Eq1 t) => Eq (LogicOp t a) where (==) = eq1


-- | Numeric operations.
data NumOp t a where
  OpAdd :: SymNum a => t a -> t a -> NumOp t a
  OpSub :: SymNum a => t a -> t a -> NumOp t a
  OpMul :: SymNum a => t a -> t a -> NumOp t a

instance Operator NumOp where
  htraverseOp f = \case
    OpAdd x y -> OpAdd <$> f x <*> f y
    OpSub x y -> OpSub <$> f x <*> f y
    OpMul x y -> OpMul <$> f x <*> f y

instance (Applicative f, Applicative g) => EvalOp f (PureEval g) NumOp where
  evalOp f = \case
    OpAdd x y -> liftA2' f symAdd x y
    OpSub x y -> liftA2' f symSub x y
    OpMul x y -> liftA2' f symMul x y


-- | Embedding literal values.
data LitOp (t :: * -> *) a where
  OpLit :: SymLit a => a -> LitOp t a

instance Operator LitOp where
  htraverseOp _ = \case
    OpLit x -> pure (OpLit x)

instance (Applicative f, Applicative g) => EvalOp f (PureEval g) LitOp where
  evalOp _ = \case
    OpLit x -> pure (pure x)

instance (Applicative f) => EvalOp f SBV LitOp where
  evalOp _ = \case
    OpLit x -> pure (toSbv x)


-- | Equality comparison.
data EqOp t a where
  OpEq :: SymEq b a => t a -> t a -> EqOp t b

instance Operator EqOp where
  htraverseOp f = \case
    OpEq x y -> OpEq <$> f x <*> f y

instance (Applicative f, Applicative g) => EvalOp f (PureEval g) EqOp where
  evalOp f = \case
    OpEq x y -> liftA2' f symEq x y

instance HigherEq EqOp where
  liftHigherEq le _ (OpEq x1 x2) (OpEq y1 y2) = le svEq x1 y1 && le svEq x2 y2

instance (Eq1 t) => Eq1 (EqOp t) where liftEq = liftEqFromHigher

instance (Eq a, Eq1 t) => Eq (EqOp t a) where (==) = eq1


-- | Ordering.
data OrdOp t a where
  OpLT :: SymOrd b a => t a -> t a -> OrdOp t b
  OpLE :: SymOrd b a => t a -> t a -> OrdOp t b
  OpGT :: SymOrd b a => t a -> t a -> OrdOp t b
  OpGE :: SymOrd b a => t a -> t a -> OrdOp t b

instance Operator OrdOp where
  htraverseOp f = \case
    OpLT x y -> OpLT <$> f x <*> f y
    OpLE x y -> OpLE <$> f x <*> f y
    OpGT x y -> OpGT <$> f x <*> f y
    OpGE x y -> OpGE <$> f x <*> f y

instance (Applicative f, Applicative g) => EvalOp f (PureEval g) OrdOp where
  evalOp f = \case
    OpLT x y -> liftA2' f symLt x y
    OpLE x y -> liftA2' f symLe x y
    OpGT x y -> liftA2' f symGt x y
    OpGE x y -> liftA2' f symGe x y

instance HigherEq OrdOp where
  liftHigherEq le _ (OpLT x1 x2) (OpLT y1 y2) = le svEq x1 y1 && le svEq x2 y2
  liftHigherEq le _ (OpGT x1 x2) (OpGT y1 y2) = le svEq x1 y1 && le svEq x2 y2
  liftHigherEq le _ (OpLE x1 x2) (OpLE y1 y2) = le svEq x1 y1 && le svEq x2 y2
  liftHigherEq le _ (OpGE x1 x2) (OpGE y1 y2) = le svEq x1 y1 && le svEq x2 y2
  liftHigherEq _ _ _ _ = False

instance (Eq1 t) => Eq1 (OrdOp t) where liftEq = liftEqFromHigher

instance (Eq a, Eq1 t) => Eq (OrdOp t a) where (==) = eq1


-- | Coercion.
data CoerceOp t a where
  OpCoerce :: (SymValue a, SymValue b) => t a -> CoerceOp t b

instance Operator CoerceOp where
  htraverseOp f = \case
    OpCoerce x -> OpCoerce <$> f x

-- TODO: Evaluating coercions purely


-- | A list of the standard operators to be used in an 'Expr''.
type StandardOps = '[LitOp, BoolOp, NumOp, EqOp, OrdOp]

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

liftA2' :: (Applicative f, Applicative g) => (a -> f (g b)) -> (b -> b -> c) -> a -> a -> f (g c)
liftA2' f g x y = getCompose (liftA2 g (Compose (f x)) (Compose (f y)))

svEq :: (Typeable a, Typeable b, Eq a) => a -> b -> Bool
svEq (x :: a) (y :: b)
  | Just Refl <- eqT :: Maybe (a :~: b) = x == y
  | otherwise = False
