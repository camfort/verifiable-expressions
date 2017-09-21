{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeOperators             #-}

module Language.Expression.Scope where

import           Control.Lens

import           Language.Expression

--------------------------------------------------------------------------------
--  Classes
--------------------------------------------------------------------------------

class HBound k where
  (^>>>=) :: (HMonad h) => k h t a -> (forall b. t b -> h t' b) -> k h t' a

--------------------------------------------------------------------------------
--  Bound or free variables
--------------------------------------------------------------------------------

data BV g f a where
  -- | Bound variable
  B :: g a -> BV g f a
  -- | Free variable
  F :: f a -> BV g f a

instance HFunctor (BV g) where
  hmap = hliftM

instance HPointed (BV g) where
  hpure = F

instance HBind (BV g) where
  B x ^>>= _ = B x
  F x ^>>= f = f x

instance HMonad (BV g)

-- instance (HFoldableAt k g) => HFoldableAt k (BV g) where
--   hfoldMap = hbifoldMap . hfoldMap

instance HTraversable (BV g) where
  htraverse = hbitraverseBV pure

foldBV :: (w a -> r) -> (v a -> r) -> BV w v a -> r
foldBV f g = \case
  B x -> f x
  F y -> g y

instance HBifunctor BV where
  hbimap = hbimapBV

instance HBitraversable BV where
  hbitraverse = hbitraverseBV

hbitraverseBV :: (Functor t) => (g a -> t (g' b)) -> (f a -> t (f' b)) -> BV g f a -> t (BV g' f' b)
hbitraverseBV f g = foldBV (fmap B . f) (fmap F . g)

hbimapBV :: (g a -> g' b) -> (f a -> f' b) -> BV g f a -> BV g' f' b
hbimapBV f g = foldBV (B . f) (F . g)

instance HBifoldableAt k BV where
  hbifoldMap = foldBV

--------------------------------------------------------------------------------
--  Scopes
--------------------------------------------------------------------------------

newtype Scope g h f a = Scope { unscope :: h (BV g (h f)) a }

_Scope :: Iso (Scope g h f a) (Scope g' h' f' a') (h (BV g (h f)) a) (h' (BV g' (h' f')) a')
_Scope = iso unscope Scope

instance HFunctor h => HFunctor (Scope g h) where
  hmap f = from _Scoped %~ hfirst f

instance HPointed h => HPointed (Scope g h) where
  hpure = Scope . hpure . hpure . hpure

instance HTraversable h => HTraversable (Scope g h) where
  htraverse f = _Scope %%~ htraverse (htraverse (htraverse f))


instance HDuofunctor (Scope g) where
  hduomap g f = _Scope %~ g (hmap (g f))

instance HDuotraversable (Scope g) where
  hduotraverse g f = _Scope %%~ g (htraverse (g f))


instance HBound (Scope g) where
  Scope x ^>>>= f = Scope (x ^>>= foldBV (hpure . B) (hmap (F . f)))


hbitraverseScope
  :: (Applicative t, HTraversable h)
  => (forall b. g b -> t (g' b))
  -> (forall b. f b -> t (f' b))
  -> Scope g h f a
  -> t (Scope g' h f' a)
hbitraverseScope g f = from _Scoped %%~ hbitraverse f g


freeVar :: (HPointed h) => f a -> Scope g h f a
freeVar = Scope . hpure . hpure . hpure


boundVar :: (HPointed h) => g a -> Scope g h f a
boundVar = Scope . hpure . B


liftScope :: (HFunctor h, HPointed h) => h f a -> Scope g h f a
liftScope = Scope . hmap (hpure . hpure)


abstractTraverse :: (HMonad h, HTraversable h, Applicative t) => (forall b. f b -> t (Maybe (g b))) -> h f a -> t (Scope g h f a)
abstractTraverse f = fmap Scope . htraverse (\y -> maybe ((hpure . hpure) y) B <$> f y)


abstract :: (HMonad h) => (forall b. f b -> Maybe (g b)) -> h f a -> Scope g h f a
abstract f = Scope . hmap (\y -> maybe ((hpure . hpure) y) B $ f y)


-- instantiate :: (Substitutive op, Applicative f) => (forall b. w b -> f (op v b)) -> Scope g h f a -> f (op v a)
-- instantiate f (Scope x) = bindVars (foldBV f pure) x

-- | Sometimes it's convenient to move around the type arguments to 'Scope'.
newtype Scoped h f g a = Scoped { unscoped :: Scope g h f a }

_Scoped :: Iso (Scoped h f g a) (Scoped h' f' g' a') (Scope g h f a) (Scope g' h' f' a')
_Scoped = iso unscoped Scoped

instance HFunctor h => HFunctor (Scoped h f) where
  hmap = hsecond

instance HFunctor h => HBifunctor (Scoped h) where
  hbimap f g = _Scoped . _Scope %~ hmap (hbimap g (hmap f))

instance HTraversable h => HBitraversable (Scoped h) where
  hbitraverse f g = _Scoped . _Scope %%~ htraverse (hbitraverse g (htraverse f))

instance HTraversable h => HTraversable (Scoped h f) where
  htraverse = hbitraverse pure

--------------------------------------------------------------------------------
--  Scoped Free Monads
--------------------------------------------------------------------------------

data SFree h f a
  = SPure (f a)
  | SWrap (h (Scoped (SFree h) f) (SFree h f) a)

instance HDuofunctor h => HFunctor (SFree h) where
  hmap = hliftM

instance HPointed (SFree h) where
  hpure = SPure

instance HDuofunctor h => HBind (SFree h) where
  SPure x ^>>= f = f x
  SWrap x ^>>= f = SWrap (hduomap (\g -> (\(Scoped y) -> Scoped (y ^>>>= f)) . hmap g) (^>>= f) x)

instance HDuofunctor h => HMonad (SFree h)

instance (HDuotraversable h) => HTraversable (SFree h) where
  htraverse f = \case
    SPure x -> SPure <$> f x
    SWrap x -> SWrap <$> hduotraverse (hbitraverse f) (htraverse f) x


instance HDuofoldableAt k (Scope k) where
  hduofoldMap f g = f (hbifoldMap id (f g)) . view _Scope

instance (HFunctor h, HFoldableAt k h) => HBifoldableAt k (Scoped h) where
  hbifoldMap f g = hfoldMap (hbifoldMap g (hfoldMap f)) . view (_Scoped . _Scope)

instance (HDuotraversable h, HDuofoldableAt k h) => HFoldableAt k (SFree h) where
  hfoldMap f = \case
    SPure x -> f x
    SWrap x ->
      hduofoldMap
      (\g -> hduofoldMap hfoldMap f . view _Scoped . hsecond g)
      (hfoldMap f)
      x
