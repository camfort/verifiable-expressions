{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveDataTypeable         #-}
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
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Language.Expression.Choice where
  -- (
  -- -- * Expressions
  --   HFree'(..)
  -- , _EVar'
  -- , _EOp'
  -- , squashExpression
  -- , eop'

  -- -- * HTraversable union
  -- , OpChoice(..)
  -- , ChooseOp(..)
  -- , SubsetOp(..)
  -- ) where

import           Data.Data

-- import           Data.Functor.Classes

import           Data.Union

import           Control.Lens         hiding (op)

import           Language.Expression

--------------------------------------------------------------------------------
--  Operator List Union
--------------------------------------------------------------------------------

-- | Form the union of a list of operators. This creates an operator which is a
-- choice from one of its constituents.
--
-- For example, @'OpChoice' '[NumOp, EqOp]@ is an operator that can either
-- represent an arithmetic operation or an equality comparison.
data OpChoice ops (t :: * -> *) a where
  OpThis :: op t a -> OpChoice (op : ops) t a
  OpThat :: OpChoice ops t a -> OpChoice (op : ops) t a
  deriving (Typeable)

_OpThis :: Prism' (OpChoice (op : ops) t a) (op t a)
_OpThis = prism' OpThis $ \case
  OpThis x -> Just x
  OpThat _ -> Nothing

_OpThat :: Prism' (OpChoice (op : ops) t a) (OpChoice ops t a)
_OpThat = prism' OpThat $ \case
  OpThis _ -> Nothing
  OpThat x -> Just x

noOps :: OpChoice '[] t a -> x
noOps = \case

instance HFunctor (OpChoice '[]) where
  hmap _ = noOps

instance HTraversable (OpChoice '[]) where
  htraverse _ = noOps

instance HFoldableAt k (OpChoice '[]) where
  hfoldMap _ = noOps

-- instance HEq (OpChoice '[]) where
--   liftHEq _ _ _ = noOps

instance (HFunctor op, HFunctor (OpChoice ops)) =>
  HFunctor (OpChoice (op : ops)) where

  hmap f = \case
    OpThis x -> OpThis (hmap f x)
    OpThat x -> OpThat (hmap f x)

instance (HTraversable op, HTraversable (OpChoice ops)) =>
  HTraversable (OpChoice (op : ops)) where

  htraverse f = \case
    OpThis x -> OpThis <$> htraverse f x
    OpThat x -> OpThat <$> htraverse f x

instance (HFoldableAt k op, HFoldableAt k (OpChoice ops)) =>
  HFoldableAt k (OpChoice (op : ops)) where

  hfoldMap f = \case
    OpThis x -> hfoldMap f x
    OpThat x -> hfoldMap f x

-- instance (HEq op, HEq (OpChoice ops)) =>
--   HEq (OpChoice (op : ops)) where

--   liftHEq le eq (OpThis x) (OpThis y) = liftHEq le eq x y
--   liftHEq le eq (OpThat x) (OpThat y) = liftHEq le eq x y
--   liftHEq _ _ _ _ = False


-- instance (HEq (OpChoice ops), Eq1 t) => Eq1 (OpChoice ops t) where
--   liftEq = liftLiftEq
-- instance (Eq1 (OpChoice ops t), Eq a) => Eq (OpChoice ops t a) where
--   (==) = liftEq (==)


newtype AsOp (t :: * -> *) a op = AsOp (op t a)

makeWrapped ''AsOp

choiceToUnion :: OpChoice ops t a -> Union (AsOp t a) ops
choiceToUnion = \case
  OpThis x -> This (AsOp x)
  OpThat x -> That (choiceToUnion x)

unionToChoice :: Union (AsOp t a) ops -> OpChoice ops t a
unionToChoice = \case
  This (AsOp x) -> OpThis x
  That x -> OpThat (unionToChoice x)

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
--  Expressions over a choice of operators
--------------------------------------------------------------------------------

-- | @'HFree'' ops v a@ is a higher-order free monad over the list of operators
-- @ops@ with variables in the type @v@ and it represents a value of type @a@.
--
-- Intuitively, it represents an expression which may contain operations from
-- any of the operators in the list @ops@.
newtype HFree' ops v a = HFree' { getHFree' :: HFree (OpChoice ops) v a }
  deriving (Typeable)

deriving instance
         (Data (HFree (OpChoice ops) v a), Typeable (HFree' ops v a)) =>
         Data (HFree' ops v a)

-- instance (HEq (OpChoice ops)) => HEq (HFree' ops) where
--   liftHEq le eq (HFree' x) (HFree' y) = liftHEq le eq x y

-- instance (Eq1 v, HEq (OpChoice ops)) => Eq1 (HFree' ops v) where
--   liftEq = liftLiftEq

-- instance (Eq1 v, HEq (OpChoice ops), Eq a) => Eq (HFree' ops v a) where
--   (==) = eq1


-- TODO: Figure out type roles so these instances can be derived by
-- GeneralizedNewtypeDeriving

instance (HFunctor (OpChoice ops)) => HFunctor (HFree' ops) where
  hmap f = HFree' . hmap f . getHFree'

instance (HTraversable (OpChoice ops)) => HTraversable (HFree' ops) where
  htraverse f = fmap HFree' . htraverse f . getHFree'

instance HPointed (HFree' ops) where
  hpure = HFree' . hpure

instance (HFunctor (OpChoice ops)) => HBind (HFree' ops) where
  x ^>>= f = (HFree' . (^>>= (getHFree' . f)) . getHFree') x

instance (HFunctor (OpChoice ops)) => HMonad (HFree' ops) where

instance (HFoldableAt k (OpChoice ops), HFunctor (OpChoice ops)) =>
         HFoldableAt k (HFree' ops) where
  hfoldMap f (HFree' x) = hfoldMap f x

-- | Squash a composition of expressions over different operators into a
-- single-layered expression over a choice of the two operators.
squashExpression
  :: (HFunctor op1,
      HFunctor op2,
      HFunctor (OpChoice ops),
      ChooseOp op1 ops,
      ChooseOp op2 ops)
  => HFree op1 (HFree op2 v) a -> HFree' ops v a
squashExpression
  = HFree'
  . hjoin
  . hmap (hduomapFirst' (review chooseOp))
  . hduomapFirst' (review chooseOp)
  -- (review chooseOp)

hwrap'
  :: (HFunctor op, HFunctor (OpChoice ops), ChooseOp op ops)
  => op (HFree' ops v) a -> HFree' ops v a
hwrap' = HFree' . HWrap . review chooseOp . hmap getHFree'

--------------------------------------------------------------------------------
--  Lenses
--------------------------------------------------------------------------------

makeWrapped ''HFree'
