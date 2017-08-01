{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}

{-|

A collection of standard operator types which may be used to form expressions.

-}
module Language.Expression.Operators
  (
  -- * Standard operators
    BoolOp(..)
  , EqOp(..)
  , OrdOp(..)
  , LitOp(..)
  , NumOp(..)

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
import           Data.Functor.Compose

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

-- | Logical operations.
data BoolOp t a where
  OpNot :: SymBool b => t b -> BoolOp t b
  OpAnd :: SymBool b => t b -> t b -> BoolOp t b
  OpOr :: SymBool b => t b -> t b -> BoolOp t b
  OpImpl :: SymBool b => t b -> t b -> BoolOp t b
  OpEquiv :: SymBool b => t b -> t b -> BoolOp t b

-- | Numeric operations.
data NumOp t a where
  OpAdd :: SymNum a => t a -> t a -> NumOp t a
  OpSub :: SymNum a => t a -> t a -> NumOp t a
  OpMul :: SymNum a => t a -> t a -> NumOp t a

-- | Embedding literal values.
data LitOp (t :: * -> *) a where
  OpLit :: SymLit a => a -> LitOp t a

-- | Equality comparison.
data EqOp t a where
  OpEq :: SymEq b a => t a -> t a -> EqOp t b

-- | Ordering.
data OrdOp t a where
  OpLT :: SymOrd b a => t a -> t a -> OrdOp t b
  OpLE :: SymOrd b a => t a -> t a -> OrdOp t b
  OpGT :: SymOrd b a => t a -> t a -> OrdOp t b
  OpGE :: SymOrd b a => t a -> t a -> OrdOp t b

-- data CoercionOp t a where
--   OpCoerce :: SymCoercible a b => t a -> CoercionOp t b

instance Operator BoolOp where
  htraverseOp f = \case
    OpNot x -> OpNot <$> f x
    OpAnd x y -> OpAnd <$> f x <*> f y
    OpOr x y -> OpOr <$> f x <*> f y
    OpImpl x y -> OpImpl <$> f x <*> f y
    OpEquiv x y -> OpEquiv <$> f x <*> f y

instance (Applicative f, Applicative g) => EvalOp f (PureEval g) BoolOp where
  evalOp f = \case
    OpNot x -> fmap symNot <$> f x
    OpAnd x y -> liftA2' f symAnd x y
    OpOr x y -> liftA2' f symOr x y
    OpImpl x y -> liftA2' f symImpl x y
    OpEquiv x y -> liftA2' f symEquiv x y

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

instance Operator LitOp where
  htraverseOp _ = \case
    OpLit x -> pure (OpLit x)

instance (Applicative f) => EvalOp f SBV LitOp where
  evalOp _ = \case
    OpLit x -> pure (toSbv x)

instance (Applicative f, Applicative g) => EvalOp f (PureEval g) LitOp where
  evalOp _ = \case
    OpLit x -> pure (pure x)

instance Operator EqOp where
  htraverseOp f = \case
    OpEq x y -> OpEq <$> f x <*> f y

instance (Applicative f, Applicative g) => EvalOp f (PureEval g) EqOp where
  evalOp f = \case
    OpEq x y -> liftA2' f symEq x y

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

-- | A list of the standard operators to be used in an 'Expr''.
type StandardOps = '[LitOp, BoolOp, NumOp, EqOp, OrdOp]

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

liftA2' :: (Applicative f, Applicative g) => (a -> f (g b)) -> (b -> b -> c) -> a -> a -> f (g c)
liftA2' f g x y = getCompose (liftA2 g (Compose (f x)) (Compose (f y)))
