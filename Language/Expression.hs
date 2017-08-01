{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Language.Expression
  (
  -- * Classes
    Operator(..)
  , Substitutive(..)
  , EvalOp(..)
  , evalOp'
  -- * Expressions
  , Expr(..)
  , Expr'(..)
  -- * Operator union
  , OpChoice(..)
  , ChooseOp(..)
  ) where

import           Control.Lens          (Prism', prism')
import           Data.Functor.Identity

--------------------------------------------------------------------------------
--  Type Classes
--------------------------------------------------------------------------------

-- | The class of operators, i.e. higher-order traversables.
class Operator op where
  -- | An operator is a higher order traversable over operands.
  htraverseOp :: (Applicative f) => (forall b. t b -> f (t' b)) -> op t a -> f (op t' a)

  -- | An operator is a higher order functor over operands.
  hmapOp :: (forall b. t b -> t' b) -> op t a -> op t' a
  hmapOp f = runIdentity . htraverseOp (Identity . f)

-- | The class of expressions which contain variables that can be substituted,
-- i.e. higher-order monads.
class (Operator expr) => Substitutive expr where
  -- | Create an expression consisting of just the given variable.
  --
  -- This is the higher-order version of 'return'.
  pureVar :: v a -> expr v a

  -- | Substitute all variables in the expression with a new expression.
  --
  -- This is the higher-order version of '(>>=)'.
  bindVars :: (forall b. v b -> expr v' b) -> expr v a -> expr v' a

-- | Some operators can be evaluated in particular contexts.
--
-- Notice we need `f (g a)` rather than collapsing `'Compose' f g` into a single
-- type variable. This gets around the situation where `g` is a type constructor
-- that doesn't make sense to be applied to just anything (e.g. 'Data.SBV.SBV'),
-- while `f` is a general context, e.g. an applicative or monad.
class (Operator op) => EvalOp f g op where
  evalOp :: (forall b. t b -> f (g b)) -> op t a -> f (g a)

-- | A convenience function for when an operator can be evaluated with no
-- context.
evalOp' :: EvalOp Identity g op => (forall b. t b -> g b) -> op t a -> g a
evalOp' f = runIdentity . evalOp (Identity . f)

--------------------------------------------------------------------------------
--  Operator List Union
--------------------------------------------------------------------------------

-- | Form the union of a list of operators. This creates an operator which is a
-- choice from one of its constituents.
--
-- For example, @'OpChoice' '[NumOp, EqOp]@ is an operator that can either
-- represent an arithmetic operation or an equality comparison.
data OpChoice ops (t :: * -> *) a where
  Op0 :: op t a -> OpChoice (op : ops) t a
  OpS :: OpChoice ops t a -> OpChoice (op : ops) t a

_Op0 :: Prism' (OpChoice (op : ops) t a) (op t a)
_Op0 = prism' Op0 $ \case
  Op0 x -> Just x
  OpS _ -> Nothing

_OpS :: Prism' (OpChoice (op : ops) t a) (OpChoice ops t a)
_OpS = prism' OpS $ \case
  Op0 _ -> Nothing
  OpS x -> Just x

instance Operator (OpChoice '[]) where
  htraverseOp _ x = case x of {}
    -- absurd

instance EvalOp f t (OpChoice '[]) where
  evalOp x = case x of {}
    -- absurd

instance (Operator op, Operator (OpChoice ops)) => Operator (OpChoice (op : ops)) where
  htraverseOp f = \case
    Op0 x -> Op0 <$> htraverseOp f x
    OpS x -> OpS <$> htraverseOp f x

instance (EvalOp f t op, EvalOp f t (OpChoice ops)) => EvalOp f t (OpChoice (op : ops)) where
  evalOp f = \case
    Op0 x -> evalOp f x
    OpS x -> evalOp f x

-- | This class provides a low-boilerplate way of lifting individual operators
-- into a union, and extracting operators from a union.
class ChooseOp op ops where
  -- | Project a single operator from a union which contains it.
  chooseOp :: Prism' (OpChoice ops t a) (op t a)

instance {-# OVERLAPPING #-} ChooseOp op (op : ops) where
  chooseOp = _Op0

instance {-# OVERLAPPABLE #-} ChooseOp op ops => ChooseOp op (op' : ops) where
  chooseOp = _OpS . chooseOp

--------------------------------------------------------------------------------
--  Expressions
--------------------------------------------------------------------------------

-- | An expression @'Expr' op v a@ has operations defined by the type @op@,
-- variables in the type @v@ and it represents a value of type @a@.
--
-- This is a higher-order free monad over the @op@ higher-order functor.
data Expr op v a
  = EVar (v a)
  | EOp (op (Expr op v) a)

-- | Variables in an expression can be substituted.
instance (Operator op) => Substitutive (Expr op) where
  pureVar = EVar

  bindVars f = \case
    EVar x -> f x
    EOp op -> EOp $ hmapOp (bindVars f) op

-- | It turns out an expression can be treated as an operator. "Variables"
-- become operator argument positions.
instance (Operator op) => Operator (Expr op) where
  htraverseOp f = \case
    EVar x -> EVar <$> f x
    EOp op -> EOp <$> htraverseOp (htraverseOp f) op

-- | Expressions can be evaluated whenever the contained operators can be
-- evaluated.
instance (EvalOp f t op) => EvalOp f t (Expr op) where
  evalOp f = \case
    EVar x -> f x
    EOp op -> evalOp (evalOp f) op

-- | An expression @'Expr'' ops v a@ has operations from the type-level list
-- @ops@, variables in the type @v@ and it represents a value of type @a@.
--
-- Intuitively, it represents an expression which may contain operations from
-- any of the operators in the list @ops@.
newtype Expr' ops v a = Expr' { getExpr' :: Expr (OpChoice ops) v a }

-- TODO: Figure out type roles so these instances can be derived by
-- GeneralizedNewtypeDeriving

instance (Operator (OpChoice ops)) => Operator (Expr' ops) where
  htraverseOp f = fmap Expr' . htraverseOp f . getExpr'

instance (Operator (OpChoice ops)) => Substitutive (Expr' ops) where
  pureVar = Expr' . pureVar

  bindVars f = Expr' . bindVars (getExpr' . f) . getExpr'

instance (EvalOp f g (OpChoice ops)) => EvalOp f g (Expr' ops) where
  evalOp f = evalOp f . getExpr'
