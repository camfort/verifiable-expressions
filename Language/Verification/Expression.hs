{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fno-warn-missing-pattern-synonym-signatures #-}

module Language.Verification.Expression where

import           Data.Functor.Compose
import           Data.Functor.Identity

--------------------------------------------------------------------------------
--  Type Classes
--------------------------------------------------------------------------------

-- | The class of operators, i.e. higher-order traversables.
class Operator op where
  -- | An operator is a higher order traversable over operands.
  traverseOp :: (Applicative f) => (forall b. t b -> f (t' b)) -> op t a -> f (op t' a)

  -- | An operator can be folded whenever its operands are applicative.
  evalOp :: (Applicative t) => op t a -> t a

  -- | An operator is a higher order functor over operands.
  mapOp :: (forall b. t b -> t' b) -> op t a -> op t' a
  mapOp f = runIdentity . traverseOp (Identity . f)

-- | The class of expressions which contain variables that can be substituted,
-- i.e. higher-order monads.
class (Operator expr) => Substitutive expr where
  pureVar :: v a -> expr v a
  bindVars :: (forall b. v b -> expr v' b) -> expr v a -> expr v' a

--------------------------------------------------------------------------------
--  Operator Union
--------------------------------------------------------------------------------

infixl 5 :+:

-- | The union of two operators is an operator.
data (o1 :+: o2) (t :: * -> *) a
  = OpLeft (o1 t a)
  | OpRight (o2 t a)

instance (Operator o1, Operator o2) => Operator (o1 :+: o2) where
  traverseOp f = \case
    OpLeft op -> OpLeft <$> traverseOp f op
    OpRight op -> OpRight <$> traverseOp f op

  evalOp = \case
    OpLeft op -> evalOp op
    OpRight op -> evalOp op

--------------------------------------------------------------------------------
--  Operator List Union
--------------------------------------------------------------------------------

-- | The union of arbitrarily many operators is an operator.
data OpChoice ops (t :: * -> *) a where
  Op0 :: op t a -> OpChoice (op : ops) t a
  OpS :: OpChoice ops t a -> OpChoice (op : ops) t a


instance Operator (OpChoice '[]) where
  traverseOp _ x = case x of {}
    -- absurd

  evalOp x = case x of {}
    -- absurd

instance (Operator op, Operator (OpChoice ops)) => Operator (OpChoice (op : ops)) where
  traverseOp f = \case
    Op0 x -> Op0 <$> traverseOp f x
    OpS x -> OpS <$> traverseOp f x

  evalOp = \case
    Op0 x -> evalOp x
    OpS x -> evalOp x

pattern Op1 x = OpS (Op0 x)
pattern Op2 x = OpS (Op1 x)
pattern Op3 x = OpS (Op2 x)
pattern Op4 x = OpS (Op3 x)
pattern Op5 x = OpS (Op4 x)
pattern Op6 x = OpS (Op5 x)
pattern Op7 x = OpS (Op6 x)

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

-- | 'Expr' is a higher-order traversable over variables.
traverseVars
  :: (Applicative f, Operator op)
  => (forall b. v b -> f (v' b))
  -> Expr op v a -> f (Expr op v' a)
traverseVars = traverseOp

-- | Variables in an expression can be substituted.
instance (Operator op) => Substitutive (Expr op) where
  pureVar = EVar

  bindVars f = \case
    EVar x -> f x
    EOp op -> EOp $ mapOp (bindVars f) op

-- | Given a way to evaluate variables, evaluate the whole expression.
evalExpr :: (Applicative f, Operator op) => (forall b. v b -> f b) -> Expr op v a -> f a
evalExpr evalVar = evalOp . mapOp evalVar

-- | It turns out an expression can be treated as an operator. "Variables"
-- become operator argument positions.
instance (Operator op) => Operator (Expr op) where
  traverseOp f = \case
    EVar x -> EVar <$> f x
    EOp op -> EOp <$> traverseOp (traverseOp f) op
  evalOp = \case
    EVar x -> x
    EOp op -> evalOp (mapOp evalOp op)

-- instance (Operator op, Functor f) => Functor (Expr op f) where
--   fmap f = \case
--     EVar x -> EVar (fmap f x)
--     EOp op -> _

--------------------------------------------------------------------------------
--  Hoisting
--------------------------------------------------------------------------------

-- | A particular type constructor @f@ can sometimes be /hoisted/ over an
-- operator, making the operator work over objects in @f@.
class (Operator op) => HoistOp f op where
  hoistOp' :: op (Compose g f) a -> op g (f a)

  hoistOp :: (forall b. f b -> g (f b)) -> op f a -> op g (f a)
  hoistOp f = hoistOp' . mapOp (Compose . f)

-- | If @f@ can be hoisted over an operator @op@, then it can also be hoisted
-- over the free monad formed by @op@.
instance HoistOp f op => HoistOp f (Expr op) where
  hoistOp' = \case
    EVar x -> EVar (getCompose x)
    EOp o -> EOp . hoistOp' . mapOp (Compose . hoistOp') $ o

instance (HoistOp f o1, HoistOp f o2) => HoistOp f (o1 :+: o2) where
  hoistOp' = \case
    OpLeft x -> OpLeft (hoistOp' x)
    OpRight x -> OpRight (hoistOp' x)

instance HoistOp f (OpChoice '[]) where
  hoistOp' x = case x of
    -- absurd

instance (HoistOp f op, HoistOp f (OpChoice ops)) => HoistOp f (OpChoice (op : ops)) where
  hoistOp' = \case
    Op0 x -> Op0 (hoistOp' x)
    OpS x -> OpS (hoistOp' x)
