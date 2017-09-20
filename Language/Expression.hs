{-# LANGUAGE DefaultSignatures         #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE UndecidableInstances      #-}

{-|
Implements higher-ranked equivalents of 'Functor', 'Monad', 'Foldable' and
'Traversable'.
-}
module Language.Expression where

import           Control.Applicative               (Alternative, (<|>))
import           Control.Monad                     ((<=<), (>=>))
import           Data.Monoid                       (Alt (..))
import           Data.Typeable                     (Typeable)

import           Control.Monad.Trans.Reader        (ReaderT (..))
import           Control.Monad.Trans.Except        (ExceptT (..))
import qualified Control.Monad.Trans.State.Lazy    as L
import qualified Control.Monad.Trans.State.Strict  as S
import qualified Control.Monad.Trans.Writer.Lazy   as L
import qualified Control.Monad.Trans.Writer.Strict as S

import           Data.Functor.Compose              (Compose (..))
import           Data.Functor.Const                (Const (..))
import           Data.Functor.Identity             (Identity (..))
import           Data.Functor.Product              (Product (..))
import           Data.Functor.Reverse              (Reverse (..))
import           Data.Functor.Sum                  (Sum (..))

infixr 1 ^>>=

--------------------------------------------------------------------------------
--  Functor / Monad
--------------------------------------------------------------------------------

{-|
Higher-ranked analogue of 'Functor'.
-}
class HFunctor (h :: (u -> *) -> u -> *) where
  {-|
  Higher-ranked analogue of 'fmap'. Has a default implementation in terms of
  'htraverse' for @'HTraversable' h@.
  -}
  hmap :: (forall b. t b -> t' b) -> h t a -> h t' a

  default hmap :: (HTraversable h) => (forall b. t b -> t' b) -> h t a -> h t' a
  hmap f = runIdentity . htraverse (Identity . f)

{-|
Half of the higher-ranked analogue of 'Monad'.
-}
class HPointed h where
  {-|
  Higher-ranked analogue of 'pure' or 'return'.
  -}
  hpure :: t a -> h t a

{-|
Half of the higher-ranked analogue of 'Monad'.
-}
class HBind h where
  {-|
  Higher-ranked analogue of '>>='.
  -}
  (^>>=) :: h t a -> (forall b. t b -> h t' b) -> h t' a

{-|

Higher-ranked analogue of 'Monad'.

NB there's no such thing as 'HApplicative' for a reason. Consider @f :: h t a ->
h t' a -> h ('Product' t t') a@, i.e. the higher-ranked analogue of @liftA2 (,)
:: f a -> f b -> f (a, b)@. Unfortunately @f@ can't exist, because @'Product'@
pairs up values /of the same type/, and in our constructions, @h@ potentially
contains values of many types; @a@ just happens to be the one at the top level.
There's no guarantee that the two structures will have the same types inside to
pair together.
-}
class (HFunctor h, HPointed h, HBind h) => HMonad h

{-|
Implements 'hmap' from just an 'HPointed' and 'HBind' instance. Can be used to
implement 'HFunctor' for your 'HMonad's that aren't 'HTraversable'.
-}
hliftM :: (HPointed h, HBind h) => (forall b. t b -> t' b) -> h t a -> h t' a
hliftM f x = x ^>>= hpure . f

{-|
Higher-ranked analogue of 'Control.Monad.join'.
-}
hjoin :: (HBind h) => h (h t) a -> h t a
hjoin x = x ^>>= id

--------------------------------------------------------------------------------
--  Traversable
--------------------------------------------------------------------------------

{-|
Higher-ranked analogue of 'Traversable'.
-}
class (HFunctor h) => HTraversable h where
  {-# MINIMAL htraverse | hsequence #-}

  {-|
  Higher-ranked analogue of 'traverse'.
  -}
  htraverse
    :: (Applicative f)
    => (forall b. t b -> f (t' b)) -> h t a -> f (h t' a)
  htraverse f = hsequence . hmap (Compose . f)

  {-|
  Higher-ranked analogue of 'sequenceA'.
  -}
  hsequence
    :: (Applicative f)
    => h (Compose f t) a -> f (h t a)
  hsequence = htraverse getCompose

-- | An 'HTraversable' instance lets you do something similar to 'foldMap'. For
-- a more flexible operation, see 'hfoldMap'.
hfoldMapMonoid
  :: (HTraversable h, Monoid m)
  => (forall b. t b -> m) -> h t a -> m
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

{-|
Higher-ranked analogue of 'Data.Bifunctor.Bifunctor'.
-}
class HBifunctor (h :: (k -> *) -> (k -> *) -> k -> *) where
  {-|
  Higher-ranked analogue of 'Data.Bifunctor.bimap'.
  -}
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

hbifoldMapMonoid
  :: (Monoid m, HBitraversable h)
  => (forall b. s b -> m) -> (forall b. t b -> m) -> h s t a -> m
hbifoldMapMonoid f g = getConst . hbitraverse (Const . f) (Const . g)

--------------------------------------------------------------------------------
--  (Even) Higher-Ranked Binary Classes
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

{-|
This is a more flexible, higher-ranked version of 'Foldable'. While 'Foldable'
only allows you to fold into a 'Monoid', 'HFoldable' allows you to fold into
some arbitrary type constructor @k@. This means that the instance can take
advantage of additional structure inside @k@ and @h@, to combine internal
results in different ways, rather than just the 'mappend' available to
'foldMap'.

Notice that if you have

@
instance ('Monoid' m) => 'HFoldableAt' ('Const' m) h
@

then 'hfoldMap' behaves very much like regular 'foldMap'.
-}
class HFoldableAt k h where
  hfoldMap :: (forall b. t b -> k b) -> h t a -> k a

{-|
For 'HFunctor's, provides an implementation of 'hfoldMap' in terms of a simple
'hfold'-like function.
-}
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


{-|
Higher-ranked equivalent of 'Data.Foldable.fold'.
-}
hfold :: HFoldableAt t h => h t a -> t a
hfold = hfoldMap id


-- | Fold in an applicative context.
hfoldA :: (HFoldableAt (Compose f t) h, Applicative f) => h t a -> f (t a)
hfoldA = hfoldMapA pure


-- | Fold in an applicative context.
hfoldMapA :: (HFoldableAt (Compose f k) h, Applicative f) => (forall b. t b -> f (k b)) -> h t a -> f (k a)
hfoldMapA f = getCompose . hfoldMap (Compose . f)


-- | 'hfoldTraverse' is to 'hfoldMap' as 'htraverse' is to 'hmap'.
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

{-|
@'HFree' h@ is a higher-ranked free monad over the higher-ranked functor @h@.
That means that given @'HFunctor' h@, we get @'HMonad' ('HFree' h)@ for free.
-}
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


instance HDuofoldableAt k HFree where
  hduofoldMap g f = \case
    HPure x -> f x
    HWrap x -> g (hduofoldMap g f) x


instance HTraversable h => HTraversable (HFree h) where
  htraverse f = \case
    HPure x -> HPure <$> f x
    HWrap x -> HWrap <$> htraverse (htraverse f) x


instance HDuofunctor HFree
instance HDuotraversable HFree where
  hduotraverse g f = \case
    HPure x -> HPure <$> f x
    HWrap x -> HWrap <$> g (hduotraverse g f) x

--------------------------------------------------------------------------------
--  Higher-ranked instances for standard functors
--------------------------------------------------------------------------------

--  'Compose' lifts a regular 'Functor'/'Monad'/etc into the higher-ranked
--  version

instance (Functor f) => HFunctor (Compose f) where
  hmap f = Compose . fmap f . getCompose

instance (Applicative f) => HPointed (Compose f) where
  hpure = Compose . pure

instance (Monad f) => HBind (Compose f) where
  Compose x ^>>= f = Compose (x >>= getCompose . f)

instance (Traversable f) => HTraversable (Compose f) where
  htraverse f = fmap Compose . traverse f . getCompose

-- | e.g. @('Monoid' m, 'Foldable' f) => 'HFoldableAt' ('Const' m) ('Compose' f)@
instance (Alternative g, Foldable f) => HFoldableAt g (Compose f) where
  hfoldMap f = getAlt . foldMap (Alt . f) . getCompose


--------------------------------------------------------------------------------
-- 'Product'

instance HFunctor (Product f)
instance HTraversable (Product f) where
  htraverse f (Pair x y) = Pair x <$> f y

instance HBifunctor Product
instance HBitraversable Product where
  hbitraverse f g (Pair x y) = Pair <$> f x <*> g y

instance (Alternative k) => HBifoldableAt k Product where
  hbifoldMap f g (Pair x y) = f x <|> g y

instance (Alternative k) => HFoldableAt k (Product k) where
  hfoldMap = hbifoldMap id

--------------------------------------------------------------------------------
-- 'Reverse' (note there's nothing for the instances to reverse)

instance HFunctor Reverse
instance HTraversable Reverse where
  htraverse f (Reverse x) = Reverse <$> f x

instance HPointed Reverse where
  hpure = Reverse

instance HBind Reverse where
  Reverse x ^>>= f = f x

instance HMonad Reverse

instance HFoldableAt k Reverse where
  hfoldMap f (Reverse x) = f x

--------------------------------------------------------------------------------
-- 'Sum'

instance HFunctor (Sum f)
instance HTraversable (Sum f) where
  htraverse _ (InL x) = pure (InL x)
  htraverse f (InR y) = InR <$> f y

instance HBifunctor Sum
instance HBitraversable Sum where
  hbitraverse f _ (InL x) = InL <$> f x
  hbitraverse _ g (InR y) = InR <$> g y

instance HPointed (Sum f) where
  hpure = InR

instance HBind (Sum f) where
  InL x ^>>= _ = InL x
  InR y ^>>= f = f y

instance HMonad (Sum f)

instance HBifoldableAt k Sum where
  hbifoldMap f _ (InL x) = f x
  hbifoldMap _ g (InR y) = g y

instance HFoldableAt k (Sum k) where
  hfoldMap = hbifoldMap id

--------------------------------------------------------------------------------
-- 'StateT'

instance HFunctor (S.StateT s) where
  hmap f (S.StateT k) = S.StateT (f . k)

instance HFunctor (L.StateT s) where
  hmap f (L.StateT k) = L.StateT (f . k)

--------------------------------------------------------------------------------
-- 'WriterT'

instance HFunctor (S.WriterT w) where
  hmap f (S.WriterT x) = S.WriterT (f x)

instance HFunctor (L.WriterT w) where
  hmap f (L.WriterT x) = L.WriterT (f x)

--------------------------------------------------------------------------------
-- 'ReaderT'

instance HFunctor (ReaderT r) where
  hmap f (ReaderT k) = ReaderT (f . k)

instance HPointed (ReaderT r) where
  hpure = ReaderT . const

instance HBind (ReaderT r) where
  ReaderT k ^>>= f = ReaderT (\r -> runReaderT (f (k r)) r)

instance HMonad (ReaderT r)

--------------------------------------------------------------------------------
-- ExceptT

instance HFunctor (ExceptT e) where
  hmap f (ExceptT x) = ExceptT (f x)
