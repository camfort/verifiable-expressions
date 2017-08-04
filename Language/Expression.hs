{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
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
  , HEq(..)
  , liftLiftEq

  -- * Expressions
  , Expr(..)
  , _EVar
  , _EOp
  , Expr'(..)
  , _EVar'
  , _EOp'
  , traverseOperators
  , mapOperators

  -- * Operator union
  , OpChoice(..)
  , ChooseOp(..)
  , SubsetOp(..)

  -- * Lifting functors
  , LiftOp(LiftOp)
  , liftOp
  , unliftOp

  -- * Restricted Operators
  , RestrictOp(..)
  , unrestrictOp

  -- * Simple Expressions
  , SimpleExpr(..)
  , _SVar
  , _SOp
  , _SimpleExpr
  , _SimpleExpr'
  ) where

import           Data.Data             (Typeable, Data, (:~:)(..))
import           Control.Monad (ap)

import           Data.Functor.Identity
import           Data.Functor.Compose
import           Data.Functor.Classes

import           Data.Union

import           Control.Lens hiding (op)

--------------------------------------------------------------------------------
--  Type Classes
--------------------------------------------------------------------------------

-- | The class of operators, i.e. higher-order traversables.
class Operator op where
  -- | An operator is a higher order traversable over operands.
  htraverseOp
    :: (Applicative f)
    => (forall b. t b -> f (t' b)) -> op t a -> f (op t' a)

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
  bindVars
    :: (Applicative f)
    => (forall b. v b -> f (expr v' b)) -> expr v a -> f (expr v' a)

  bindVars' :: (forall b. v b -> expr v' b) -> expr v a -> expr v' a
  bindVars' f = runIdentity . bindVars (Identity . f)

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


class HEq op where
  liftHEq
    :: (forall x y. (x -> y -> Bool) -> f x -> g y -> Bool)
    -> (a -> b -> Bool) -> op f a -> op g b -> Bool

liftLiftEq
  :: (HEq op, Eq1 t)
  => (a -> b -> Bool) -> op t a -> op t b -> Bool
liftLiftEq = liftHEq liftEq

instance (Eq1 f) => HEq (Compose f) where
  liftHEq le eq (Compose x) (Compose y) = liftEq (le eq) x y

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
  deriving (Typeable)

_Op0 :: Prism' (OpChoice (op : ops) t a) (op t a)
_Op0 = prism' Op0 $ \case
  Op0 x -> Just x
  OpS _ -> Nothing

_OpS :: Prism' (OpChoice (op : ops) t a) (OpChoice ops t a)
_OpS = prism' OpS $ \case
  Op0 _ -> Nothing
  OpS x -> Just x

choiceToUnion :: OpChoice ops t a -> Union (AsOp t a) ops
choiceToUnion = \case
  Op0 x -> This (AsOp x)
  OpS x -> That (choiceToUnion x)

unionToChoice :: Union (AsOp t a) ops -> OpChoice ops t a
unionToChoice = \case
  This (AsOp x) -> Op0 x
  That x -> OpS (unionToChoice x)

noOps :: OpChoice '[] t a -> x
noOps = \case

instance Operator (OpChoice '[]) where
  htraverseOp _ = noOps

instance EvalOp f t (OpChoice '[]) where
  evalOp _ = noOps

instance HEq (OpChoice '[]) where
  liftHEq _ _ _ = noOps

instance (Operator op, Operator (OpChoice ops)) =>
  Operator (OpChoice (op : ops)) where

  htraverseOp f = \case
    Op0 x -> Op0 <$> htraverseOp f x
    OpS x -> OpS <$> htraverseOp f x

instance (EvalOp f t op, EvalOp f t (OpChoice ops)) =>
  EvalOp f t (OpChoice (op : ops)) where

  evalOp f = \case
    Op0 x -> evalOp f x
    OpS x -> evalOp f x

instance (HEq op, HEq (OpChoice ops)) =>
  HEq (OpChoice (op : ops)) where

  liftHEq le eq (Op0 x) (Op0 y) = liftHEq le eq x y
  liftHEq le eq (OpS x) (OpS y) = liftHEq le eq x y
  liftHEq _ _ _ _ = False


instance (HEq (OpChoice ops), Eq1 t) => Eq1 (OpChoice ops t) where
  liftEq = liftLiftEq
instance (Eq1 (OpChoice ops t), Eq a) => Eq (OpChoice ops t a) where
  (==) = liftEq (==)


newtype AsOp (t :: * -> *) a op = AsOp (op t a)

makeWrapped ''AsOp

_OpChoice
  :: Iso (OpChoice ops t a) (OpChoice ops' t' a')
         (Union (AsOp t a) ops) (Union (AsOp t' a') ops')
_OpChoice = iso choiceToUnion unionToChoice

-- | This class provides a low-boilerplate way of lifting individual operators
-- into a union, and extracting operators from a union.
class ChooseOp op ops where
  -- | Project a single operator from a union which contains it.
  chooseOp :: Prism' (OpChoice ops t a) (op t a)

instance UElem op ops i => ChooseOp op ops where
  chooseOp = _OpChoice . uprism . _Wrapped


class SubsetOp ops1 ops2 where
  subsetOp :: Prism' (OpChoice ops2 t a) (OpChoice ops1 t a)

instance USubset ops1 ops2 is => SubsetOp ops1 ops2 where
  subsetOp = _OpChoice . usubset . from _OpChoice

--------------------------------------------------------------------------------
--  Lifting simple functors into operators
--------------------------------------------------------------------------------

newtype LiftOp f t a = LiftOp { getLiftOp :: Compose f t a }
  deriving (Typeable, Data, Show, Functor, Applicative, Foldable, Traversable)

unliftOp :: LiftOp f g a -> f (g a)
unliftOp = getCompose . getLiftOp

liftOp :: f (t a) -> LiftOp f t a
liftOp = LiftOp . Compose

instance Traversable f => Operator (LiftOp f) where
  htraverseOp f = fmap liftOp . traverse f . unliftOp

instance (Eq1 f) => HEq (LiftOp f) where
  liftHEq le eq (LiftOp x) (LiftOp y) = liftHEq le eq x y

instance (Eq1 f, Eq1 t) => Eq1 (LiftOp f t) where liftEq = liftLiftEq

instance (Eq1 f, Eq1 t, Eq a) => Eq (LiftOp f t a) where (==) = liftEq (==)

--------------------------------------------------------------------------------
--  Restricted Operators
--------------------------------------------------------------------------------

-- | @'RestrictOp' k op@ is an operator that behaves like @op@, but restricts
-- its value types to those types @a@ for which a proof of @k a@ can be given.
--
-- For example, if @k@ is @(':~:') Integer@, then values must be of type
-- 'Integer'.
data RestrictOp k (op :: (* -> *) -> * -> *) t a = RestrictOp (k a) (op t a)

instance Operator op => Operator (RestrictOp k op) where
  htraverseOp f (RestrictOp k x) = RestrictOp k <$> htraverseOp f x

instance (Eq1 k, HEq op) => HEq (RestrictOp k op) where
  liftHEq le eq (RestrictOp x1 x2) (RestrictOp y1 y2) =
    liftEq eq x1 y1 && liftHEq le eq x2 y2

instance (Eq1 k, Eq1 t, HEq op) => Eq1 (RestrictOp k op t) where
  liftEq = liftLiftEq

instance (Eq1 k, Eq1 t, HEq op, Eq a) => Eq (RestrictOp k op t a) where
  (==) = eq1


unrestrictOp :: RestrictOp k op t a -> op t a
unrestrictOp (RestrictOp _ x) = x

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
  deriving (Typeable)

deriving instance (Data (v a), Data (op (Expr op v) a),
                   Typeable op, Typeable v, Typeable a) => Data (Expr op v a)
deriving instance (Show (v a), Show (op (Expr op v) a)) => Show (Expr op v a)

deriving instance (Functor v, Functor (op (Expr op v))) => Functor (Expr op v)
deriving instance (Foldable v,
                   Foldable (op (Expr op v))) => Foldable (Expr op v)
deriving instance (Traversable v,
                   Traversable (op (Expr op v))) => Traversable (Expr op v)

instance (HEq op) => HEq (Expr op) where
  liftHEq le eq (EVar x) (EVar y) = le eq x y
  liftHEq le eq (EOp x) (EOp y) = liftHEq (liftHEq le) eq x y
  liftHEq _ _ _ _ = False

instance (HEq op, Eq1 v) => Eq1 (Expr op v) where liftEq = liftLiftEq
instance (HEq op, Eq1 v, Eq a) => Eq (Expr op v a) where (==) = eq1


-- | Variables in an expression can be substituted.
instance (Operator op) => Substitutive (Expr op) where
  pureVar = EVar

  bindVars f = \case
    EVar x -> f x
    EOp op -> EOp <$> htraverseOp (bindVars f) op


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


traverseOperators
  :: (Monad f, Operator op)
  => (forall b t. op t b -> f (op' t b)) -> Expr op v a -> f (Expr op' v a)
traverseOperators f = \case
  EVar x -> pure (EVar x)
  EOp op -> do
    op' <- htraverseOp (traverseOperators f) op
    EOp <$> f op'


mapOperators
  :: (Operator op)
  => (forall b t. op t b -> op' t b) -> Expr op v a -> Expr op' v a
mapOperators f = runIdentity . traverseOperators (Identity . f)

--------------------------------------------------------------------------------
--  Expressions over a choice of operators
--------------------------------------------------------------------------------

-- | An expression @'Expr'' ops v a@ has operations from the type-level list
-- @ops@, variables in the type @v@ and it represents a value of type @a@.
--
-- Intuitively, it represents an expression which may contain operations from
-- any of the operators in the list @ops@.
newtype Expr' ops v a = Expr' { getExpr' :: Expr (OpChoice ops) v a }
  deriving (Typeable)

deriving instance (Data (v a), Data (OpChoice ops (Expr (OpChoice ops) v) a),
                   Typeable ops, Typeable v, Typeable a) =>
                  Data (Expr' ops v a)

deriving instance (Functor v, Functor (OpChoice ops (Expr (OpChoice ops) v))) =>
  Functor (Expr' ops v)

deriving instance (Foldable v,
                   Foldable (OpChoice ops (Expr (OpChoice ops) v))) =>
                  Foldable (Expr' ops v)

deriving instance (Traversable v,
                   Traversable (OpChoice ops (Expr (OpChoice ops) v))) =>
                  Traversable (Expr' ops v)

instance (HEq (OpChoice ops)) => HEq (Expr' ops) where
  liftHEq le eq (Expr' x) (Expr' y) = liftHEq le eq x y

instance (Eq1 v, HEq (OpChoice ops)) => Eq1 (Expr' ops v) where
  liftEq = liftLiftEq

instance (Eq1 v, HEq (OpChoice ops), Eq a) => Eq (Expr' ops v a) where
  (==) = eq1


-- TODO: Figure out type roles so these instances can be derived by
-- GeneralizedNewtypeDeriving

instance (Operator (OpChoice ops)) => Operator (Expr' ops) where
  htraverseOp f = fmap Expr' . htraverseOp f . getExpr'

instance (Operator (OpChoice ops)) => Substitutive (Expr' ops) where
  pureVar = Expr' . pureVar

  bindVars f = fmap Expr' . bindVars (fmap getExpr' . f) . getExpr'

instance (EvalOp f g (OpChoice ops)) => EvalOp f g (Expr' ops) where
  evalOp f = evalOp f . getExpr'

--------------------------------------------------------------------------------
--  Simple expressions
--------------------------------------------------------------------------------

data SimpleExpr op a
  = SVar a
  | SOp (op (SimpleExpr op a))
  deriving (Typeable, Functor, Foldable, Traversable)

deriving instance (Typeable op, Typeable a, Data a,
                   Data (op (SimpleExpr op a))) => Data (SimpleExpr op a)

deriving instance (Show a, Show (op (SimpleExpr op a))) =>
  Show (SimpleExpr op a)

instance HEq SimpleExpr where
  liftHEq _ eq (SVar x) (SVar y) = eq x y
  liftHEq le eq (SOp x) (SOp y) = le (liftHEq le eq) x y
  liftHEq _ _ _ _ = False

instance (Eq1 op) => Eq1 (SimpleExpr op) where liftEq = liftLiftEq

instance (Eq1 op, Eq a) => Eq (SimpleExpr op a) where (==) = eq1


instance Functor op => Applicative (SimpleExpr op) where
  pure = return
  (<*>) = ap

instance Functor op => Monad (SimpleExpr op) where
  return = SVar

  e >>= f = case e of
    SVar x -> f x
    SOp x -> SOp ((>>= f) <$> x)


_SimpleExpr
  :: Functor op
  => Iso (Expr (LiftOp op) v a) (Expr (LiftOp op) v b)
         (SimpleExpr op (v a)) (SimpleExpr op (v b))
_SimpleExpr = iso toSimpleExpr fromSimpleExpr
  where
    toSimpleExpr = \case
      EVar x -> SVar x
      EOp (LiftOp (Compose x)) -> SOp (toSimpleExpr <$> x)

    fromSimpleExpr = \case
      SVar x -> EVar x
      SOp x -> EOp (liftOp (fromSimpleExpr <$> x))


_SimpleExpr'
  :: Functor op
  => Iso (Expr (RestrictOp ((:~:) a) (LiftOp op)) v a)
         (Expr (RestrictOp ((:~:) b) (LiftOp op)) v' b)
         (SimpleExpr op (v a)) (SimpleExpr op (v' b))
_SimpleExpr' = iso toSimpleExpr fromSimpleExpr
  where
    toSimpleExpr = \case
      EVar x -> SVar x
      EOp (RestrictOp _ (LiftOp (Compose x))) -> SOp (toSimpleExpr <$> x)

    fromSimpleExpr = \case
      SVar x -> EVar x
      SOp x -> EOp (RestrictOp Refl $ liftOp (fromSimpleExpr <$> x))

--------------------------------------------------------------------------------
--  TH Lenses
--------------------------------------------------------------------------------

makePrisms ''Expr
makeWrapped ''Expr'
makePrisms ''SimpleExpr

_EOp' :: Prism' (Expr' ops v a) (OpChoice ops (Expr (OpChoice ops) v) a)
_EOp' = _Wrapped . _EOp

_EVar' :: Prism' (Expr' ops v a) (v a)
_EVar' = _Wrapped . _EVar
