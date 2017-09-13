{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Expression where

import           Data.Data
import           Control.Monad ((<=<))

import           Data.Functor.Const
import           Data.Functor.Identity

infixr 1 ^>>=

--------------------------------------------------------------------------------
--  Functor / Monad
--------------------------------------------------------------------------------

class HFunctor h where
  hmap :: (forall b. t b -> t' b) -> h t a -> h t' a

class HPointed h where
  hpure :: t a -> h t a

class HBind h where
  (^>>=) :: h t a -> (forall b. t b -> h t' b) -> h t' a

-- | NB there's no such thing as 'HApplicative' for a reason. Consider @f :: h t
-- a -> h t' a -> h (Pair t t') a@, i.e. the higher-order analogue of @liftA2
-- (,) :: f a -> f b -> f (a, b)@. Unfortunately @f@ can't exist, because
-- @'Pair'@ pairs up values /of the same type/, and in our constructions, @h@
-- potentially contains values of many types; @a@ just happens to be the one at
-- the top level. There's no guarantee that the two structures will have the
-- same types inside to pair together.
class (HFunctor h, HPointed h, HBind h) => HMonad h

hliftM :: (HPointed h, HBind h) => (forall b. t b -> t' b) -> h t a -> h t' a
hliftM f x = x ^>>= hpure . f

hjoin :: (HMonad h) => h (h t) a -> h t a
hjoin x = x ^>>= id

--------------------------------------------------------------------------------
--  Foldable / Traversable
--------------------------------------------------------------------------------

class HFoldableAt t h where
  hfoldAt :: h t a -> t a

hfoldTraverseAt
  :: (HFoldableAt k h, HTraversable h, Applicative f)
  => (forall b. t b -> f (k b))
  -> h t a
  -> f (k a)
hfoldTraverseAt f = fmap hfoldAt . htraverse f

hfoldMapAt
  :: (HFoldableAt k h, HFunctor h)
  => (forall b. t b -> k b)
  -> h t a
  -> k a
hfoldMapAt f = hfoldAt . hmap f


class (HFunctor h) => HTraversable h where
  htraverse
    :: (Applicative f)
    => (forall b. t b -> f (t' b)) -> h t a -> f (h t' a)

hfoldMap :: (HTraversable h, Monoid m) => (forall b. t b -> m) -> h t a -> m
hfoldMap f = getConst . htraverse (Const . f)

hliftT :: (HTraversable h) => (forall b. t b -> t' b) -> h t a -> h t' a
hliftT f = runIdentity . htraverse (Identity . f)

hbindTraverse
  :: (HTraversable h, HMonad h, Applicative f)
  => (forall b. t b -> f (h t' b))
  -> h t a
  -> f (h t' a)
hbindTraverse f = fmap hjoin . htraverse f

--------------------------------------------------------------------------------
--  Binary Classes
--------------------------------------------------------------------------------

class HBifunctor h where
  {-# MINIMAL hbimap | hfirst, hsecond #-}

  hbimap :: (forall b. s b -> s' b)
         -> (forall b. t b -> t' b)
         -> h s t a
         -> h s' t' a
  hfirst :: (forall b. s b -> s' b) -> h s t a -> h s' t a
  hsecond :: (forall b. t b -> t' b) -> h s t a -> h s t' a

  hbimap f g = hfirst f . hsecond g
  hfirst f = hbimap f id
  hsecond = hbimap id


class HBifoldableAt k h where
  hbifoldAt :: h k k a -> k a


class (HBifunctor h) => HBitraversable h where
  hbitraverse
    :: (Applicative f)
    => (forall b. s b -> f (s' b))
    -> (forall b. t b -> f (t' b))
    -> h s t a -> f (h s' t' a)

defaultHbifoldMap :: (Monoid m, HBitraversable h) => (forall b. s b -> m) -> (forall b. t b -> m) -> h s t a -> m
defaultHbifoldMap f g = getConst . hbitraverse (Const . f) (Const . g)

defaultHbimap
  :: (HBitraversable h)
  => (forall b. s b -> s' b)
  -> (forall b. t b -> t' b)
  -> h s t a
  -> h s' t' a
defaultHbimap f g = runIdentity . hbitraverse (Identity . f) (Identity . g)

--------------------------------------------------------------------------------
--  (Even) Higher-Order Binary Classes
--------------------------------------------------------------------------------

class HDuofunctor h where
  hduomap
    :: (forall g g' b. (forall c. g c -> g' c) -> s g b -> s' g' b)
    -> (forall b. t b -> t' b)
    -> h s t a
    -> h s' t' a

hduomapFirst
  :: HDuofunctor h
  => (forall g g' b. (forall c. g c -> g' c) -> s g b -> s' g' b)
  -> h s t a
  -> h s' t a
hduomapFirst f = hduomap f id

hduomapFirst'
  :: (HDuofunctor h, HFunctor s)
  => (forall g b. s g b -> s' g b) -> h s t a -> h s' t a
hduomapFirst' f = hduomapFirst (\g -> f . hmap g)

hduomapSecond
  :: (HDuofunctor h, HFunctor s)
  => (forall b. t b -> t' b) -> h s t a -> h s t' a
hduomapSecond = hduomap hmap


class HDuofoldableAt k h where
  hduofoldMapAt :: (forall g b. (forall c. g c -> k c) -> s g b -> k b) -> h s k a -> k a


class HDuofunctor h => HDuotraversable h where
  hduotraverse
    :: (Applicative f)
    => (forall g g' b. (forall c. g c -> f (g' c)) -> s g b -> f (s' g' b))
    -> (forall b. t b -> f (t' b))
    -> h s t a
    -> f (h s' t' a)

defaultHduomap
  :: (HDuotraversable h)
  => (forall g g' b. (forall c. g c -> g' c) -> s g b -> s' g' b)
  -> (forall b. t b -> t' b)
  -> h s t a
  -> h s' t' a
defaultHduomap f g =
  runIdentity .
  hduotraverse (\h -> Identity . f (runIdentity . h)) (Identity . g)

hduotraverseFirst
  :: (HDuotraversable h, Applicative f)
  => (forall g g' b. (forall c. g c -> f (g' c)) -> s g b -> f (s' g' b))
  -> h s t a
  -> f (h s' t a)
hduotraverseFirst f = hduotraverse f pure

hduotraverseFirst'
  :: (HDuotraversable h, HTraversable s, Monad f)
  => (forall g b. s g b -> f (s' g b)) -> h s t a -> f (h s' t a)
hduotraverseFirst' f = hduotraverseFirst (\g -> f <=< htraverse g)

hduotraverseSecond
  :: (HDuotraversable h, HTraversable s, Applicative f)
  => (forall b. t b -> f (t' b)) -> h s t a -> f (h s t' a)
hduotraverseSecond = hduotraverse htraverse

--------------------------------------------------------------------------------
--  Free Monads
--------------------------------------------------------------------------------

data HFree h t a
  = HPure (t a)
  | HWrap (h (HFree h t) a)
  deriving (Typeable)

instance HFunctor h => HFunctor (HFree h) where
  hmap = hliftM

instance HPointed (HFree h) where
  hpure = HPure

instance HFunctor h => HBind (HFree h) where
  HPure x ^>>= f = f x
  HWrap x ^>>= f = HWrap (hmap (^>>= f) x)

instance HFunctor h => HMonad (HFree h)


instance (HFunctor h, HFoldableAt k h) => HFoldableAt k (HFree h) where
  hfoldAt = \case
    HPure x -> x
    HWrap x -> hfoldMapAt hfoldAt x


instance HTraversable h => HTraversable (HFree h) where
  htraverse f = \case
    HPure x -> HPure <$> f x
    HWrap x -> HWrap <$> htraverse (htraverse f) x


instance HDuofunctor HFree where
  hduomap = defaultHduomap

instance HDuotraversable HFree where
  hduotraverse f g = \case
    HPure x -> HPure <$> g x
    HWrap x -> HWrap <$> f (hduotraverse f g) x


deriving instance
         (Typeable (HFree h t a), Data (h (HFree h t) a), Data (t a)) =>
         Data (HFree h t a)

--------------------------------------------------------------------------------
--  Functors
--------------------------------------------------------------------------------

data Pair f g a = Pair (f a) (g a)
