{-# LANGUAGE TypeFamilies          #-}
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

module Language.Expression where

import           Data.Functor.Compose
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
  pureVar :: v a -> expr v a
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
--  Operator Union
--------------------------------------------------------------------------------

infixl 5 :+:

-- | The union of two operators is an operator.
data (o1 :+: o2) (t :: * -> *) a
  = OpLeft (o1 t a)
  | OpRight (o2 t a)

instance (Operator o1, Operator o2) => Operator (o1 :+: o2) where
  htraverseOp f = \case
    OpLeft op -> OpLeft <$> htraverseOp f op
    OpRight op -> OpRight <$> htraverseOp f op

instance (EvalOp f t o1, EvalOp f t o2) => EvalOp f t (o1 :+: o2) where
  evalOp f = \case
    OpLeft op -> evalOp f op
    OpRight op -> evalOp f op

--------------------------------------------------------------------------------
--  Operator List Union
--------------------------------------------------------------------------------

-- | The union of arbitrarily many operators is an operator.
data OpChoice ops (t :: * -> *) a where
  Op0 :: op t a -> OpChoice (op : ops) t a
  OpS :: OpChoice ops t a -> OpChoice (op : ops) t a


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
traverseVars = htraverseOp

-- | Variables in an expression can be substituted.
instance (Operator op) => Substitutive (Expr op) where
  pureVar = EVar

  bindVars f = \case
    EVar x -> f x
    EOp op -> EOp $ hmapOp (bindVars f) op

-- | Given a way to evaluate variables, evaluate the whole expression.
evalExpr
  :: (EvalOp f t op)
  => (forall b. v b -> f (t b))
  -> Expr op v a
  -> f (t a)
evalExpr = evalOp

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

--------------------------------------------------------------------------------
--  Hoisting
--------------------------------------------------------------------------------

-- | A particular type constructor @f@ can sometimes be /hoisted/ over an
-- operator, making the operator work over objects in @t@.
class (Operator op) => HoistOp t op where
  -- {-# MINIMAL hoistOp | hoistOp' #-}

  hoistOp :: (forall b. f b -> g (t b)) -> op f a -> op g (t a)
  hoistOp f = hoistOp' . hmapOp (Compose . f)

  hoistOp' :: op (Compose f t) a -> op f (t a)
  hoistOp' = hoistOp getCompose

-- | If @f@ can be hoisted over an operator @op@, then it can also be hoisted
-- over the free monad formed by @op@.
instance HoistOp f op => HoistOp f (Expr op) where
  hoistOp f = \case
    EVar x -> EVar . f $ x
    EOp o -> EOp . hoistOp getCompose . hmapOp (Compose . hoistOp f) $ o

instance (HoistOp f o1, HoistOp f o2) => HoistOp f (o1 :+: o2) where
  hoistOp f = \case
    OpLeft x -> OpLeft (hoistOp f x)
    OpRight x -> OpRight (hoistOp f x)

instance HoistOp f (OpChoice '[]) where
  hoistOp _ x = case x of
    -- absurd

instance (HoistOp f op, HoistOp f (OpChoice ops)
         ) => HoistOp f (OpChoice (op : ops)) where

  hoistOp f = \case
    Op0 x -> Op0 (hoistOp f x)
    OpS x -> OpS (hoistOp f x)
