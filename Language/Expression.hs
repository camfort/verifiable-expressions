{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE NoMonomorphismRestriction     #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE PolyKinds  #-}

module Language.Expression where

import           Control.Monad         ((>=>), (<=<))
import           Data.Data

import           Data.Functor.Const
import           Data.Functor.Identity
import           Data.Functor.Compose

infixr 1 ^>>=

--------------------------------------------------------------------------------
--  Functor / Monad
--------------------------------------------------------------------------------

class HFunctor (h :: (u -> *) -> u -> *) where
  hmap :: (forall b. t b -> t' b) -> h t a -> h t' a

  default hmap :: (HTraversable h) => (forall b. t b -> t' b) -> h t a -> h t' a
  hmap f = runIdentity . htraverse (Identity . f)

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
--  Traversable
--------------------------------------------------------------------------------

class (HFunctor h) => HTraversable h where
  htraverse
    :: (Applicative f)
    => (forall b. t b -> f (t' b)) -> h t a -> f (h t' a)

hfoldMapMonoid :: (HTraversable h, Monoid m) => (forall b. t b -> m) -> h t a -> m
hfoldMapMonoid f = getConst . htraverse (Const . f)

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
  {-# MINIMAL hbimap #-}

  hbimap :: (forall b. s b -> s' b)
         -> (forall b. t b -> t' b)
         -> h s t a
         -> h s' t' a
  hfirst :: (forall b. s b -> s' b) -> h s t a -> h s' t a
  hsecond :: (forall b. t b -> t' b) -> h s t a -> h s t' a

  default hbimap
    :: (HBitraversable h)
    => (forall b. s b -> s' b)
    -> (forall b. t b -> t' b)
    -> h s t a
    -> h s' t' a
  hbimap f g = runIdentity . hbitraverse (Identity . f) (Identity . g)

  hfirst f = hbimap f id
  hsecond = hbimap id

class (HBifunctor h) => HBitraversable h where
  hbitraverse
    :: (Applicative f)
    => (forall b. s b -> f (s' b))
    -> (forall b. t b -> f (t' b))
    -> h s t a -> f (h s' t' a)

-- hbifoldMap :: (Monoid m, HBitraversable h) => (forall b. s b -> m) -> (forall b. t b -> m) -> h s t a -> m
-- hbifoldMap f g = getConst . hbitraverse (Const . f) (Const . g)

--------------------------------------------------------------------------------
--  (Even) Higher-Order Binary Classes
--------------------------------------------------------------------------------

class HDuofunctor (h :: ((u -> *) -> u -> *) -> (u -> *) -> u -> *) where
  hduomap
    :: (forall g g' b. (forall c. g c -> g' c) -> s g b -> s' g' b)
    -> (forall b. t b -> t' b)
    -> h s t a
    -> h s' t' a

  default hduomap
    :: (HDuotraversable h)
    => (forall g g' b. (forall c. g c -> g' c) -> s g b -> s' g' b)
    -> (forall b. t b -> t' b)
    -> h s t a
    -> h s' t' a
  hduomap f g =
    runIdentity .
    hduotraverse (\h -> Identity . f (runIdentity . h)) (Identity . g)

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

class HDuofunctor h => HDuotraversable h where
  hduotraverse
    :: (Applicative f)
    => (forall g g' b. (forall c. g c -> f (g' c)) -> s g b -> f (s' g' b))
    -> (forall b. t b -> f (t' b))
    -> h s t a
    -> f (h s' t' a)

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
--  Folding
--------------------------------------------------------------------------------

class HFoldableAt k h where
  hfoldMap :: (forall b. t b -> k b) -> h t a -> k a

implHfoldMap
  :: (HFunctor h)
  => (h k a -> k a)
  -> (forall b. t b -> k b) -> h t a -> k a
implHfoldMap g f = g . hmap f

-- | A helper function for implementing instances with the general form @'Monad'
-- m => 'HFoldableAt' ('Compose' m t) h@. I.e. folding that requires a monadic
-- context of some kind.
implHfoldMapCompose
  :: (HTraversable h, Monad m)
  => (h k a -> m (k a))
  -> (forall b. t b -> Compose m k b) -> h t a -> Compose m k a
implHfoldMapCompose f = implHfoldMap (Compose . (htraverse getCompose >=> f))


hfold :: HFoldableAt t h => h t a -> t a
hfold = hfoldMap id


-- | Fold in an applicative context.
hfoldA :: (HFoldableAt (Compose f t) h, Applicative f) => h t a -> f (t a)
hfoldA = hfoldMapA pure


-- | Fold in an applicative context.
hfoldMapA :: (HFoldableAt (Compose f k) h, Applicative f) => (forall b. t b -> f (k b)) -> h t a -> f (k a)
hfoldMapA f = getCompose . hfoldMap (Compose . f)


hfoldTraverse
  :: (HFoldableAt k h, HTraversable h, Applicative f)
  => (forall b. t b -> f (k b))
  -> h t a
  -> f (k a)
hfoldTraverse f = fmap hfold . htraverse f


class HBifoldableAt k h where
  hbifoldMap :: (forall b. f b -> k b) -> (forall b. g b -> k b) -> h f g a -> k a

hbifold :: (HBifoldableAt k h) => h k k a -> k a
hbifold = hbifoldMap id id


class HDuofoldableAt k h where
  hduofoldMap
    :: (HTraversable s)
    => (forall g b. (forall c. g c -> k c) -> s g b -> k b)
    -> (forall b. t b -> k b)
    -> h s t a
    -> k a


implHduofoldMap
  :: (HDuofunctor h, HFunctor s)
  => ((forall g b. (forall c. g c -> k c) -> s g b -> k b) -> h s k a -> k a)
  -> (forall g b. (forall c. g c -> k c) -> s g b -> k b)
  -> (forall b. t b -> k b)
  -> h s t a
  -> k a
implHduofoldMap h f g = h f . hduomap hmap g


implHduofoldMapCompose
  :: (HDuotraversable h, HTraversable s, Monad m)
  => ((forall g b. (forall c. g c -> m (k c)) -> s g b -> m (k b)) -> h s k a -> m (k a))
  -> (forall g b. (forall c. g c -> Compose m k c) -> s g b -> Compose m k b)
  -> (forall b. t b -> Compose m k b)
  -> h s t a
  -> Compose m k a
implHduofoldMapCompose f =
  implHduofoldMap
    (\g ->
       Compose .
       (hduotraverseSecond getCompose >=>
        f (\h -> getCompose . g (Compose . h))))

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


instance (HFoldableAt k h) => HFoldableAt k (HFree h) where
  hfoldMap f = \case
    HPure x -> f x
    HWrap x -> hfoldMap (hfoldMap f) x


instance HTraversable h => HTraversable (HFree h) where
  htraverse f = \case
    HPure x -> HPure <$> f x
    HWrap x -> HWrap <$> htraverse (htraverse f) x


instance HDuofunctor HFree
instance HDuotraversable HFree where
  hduotraverse g f = \case
    HPure x -> HPure <$> f x
    HWrap x -> HWrap <$> g (hduotraverse g f) x
