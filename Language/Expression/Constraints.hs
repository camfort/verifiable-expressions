{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Language.Expression.Constraints
  (
  -- * Existential types
    Exists(..)
  , _Exists
  , Exists2(..)
  , _Exists2
  , toExists2
  , exTypeRep
  , ex2TypeReps
  , gcast2'

  -- * Type maps
  , Typemap
  , Typemap2
  , typemapEntry
  , typemap2Entry
  , hmapTypemap
  , hmapTypemap2
  , toTypemap2

  -- * Dictionaries for classes
  , Dict(..)
  , Dict1(..)
  , pattern Dict1
  , Dict2(..)
  , pattern Dict2

  -- * Type maps specialized to classes
  , Dictmap
  , Dictmap2
  , dictmap
  , dictmapEntry
  , dictmap2Entry
  , withDictmap
  , withDictmap2
  , withDictmap2'
  , toDictmap2

  -- * Constraints over each type in a list
  , HaveInstances(..)
  ) where

import           Data.Typeable

import           Data.Map        (Map)
import qualified Data.Map        as Map

import           Control.Lens
import           Data.Constraint

-- * Existential Types

-- | @'Exists' p@ contains @p a@ for some @a@, which can be dynamically
-- inspected through 'Typeable'.
data Exists p where
  Exists :: Typeable a => p a -> Exists p


-- | @'Exists2' p@ contains @p a b@ for some @a@ and @b@, which can be
-- dynamically inspected through 'Typeable'.
data Exists2 p where
  Exists2 :: (Typeable a, Typeable b) => p a b -> Exists2 p


-- | Project the contents of an existential at a particular type. Fails if you
-- try to project the wrong type.
_Exists :: forall a b p. (Typeable a, Typeable b) => Prism (Exists p) (Exists p) (p a) (p b)
_Exists = prism Exists extract
  where
    extract (Exists d) =
      maybe (Left (Exists d)) Right $ gcast d


-- | Project the contents of a 2-existential at particular types. Fails if you
-- try to project the wrong types.
_Exists2
  :: forall a b c d p.
     (Typeable a, Typeable b, Typeable c, Typeable d)
  => Prism (Exists2 p) (Exists2 p) (p a b) (p c d)
_Exists2 = prism Exists2 extract
  where
    extract (Exists2 d) =
      maybe (Left (Exists2 d)) Right $ gcast2' d


toExists2 :: (Typeable a) => Exists (p a) -> Exists2 p
toExists2 (Exists d) = Exists2 d


-- | Like 'gcast' from "Data.Typeable", but casts the two type arguments of a
-- binary type constructor.
gcast2'
  :: forall a b c d p. (Typeable a, Typeable b, Typeable c, Typeable d)
  => p a b -> Maybe (p c d)
gcast2' x
  | Just Refl <- eqT :: Maybe (a :~: c)
  , Just Refl <- eqT :: Maybe (b :~: d) = Just x
  | otherwise = Nothing


-- | Retrieve the 'TypeRep' for the type @a@ which is hidden inside the
-- existential.
exTypeRep :: Exists p -> TypeRep
exTypeRep (Exists (proxy :: p a)) = typeRep proxy


-- | Retrieve the 'TypeRep's for the types @a@ and @b@ which are hidden inside the
-- existential.
ex2TypeReps :: Exists2 p -> (TypeRep, TypeRep)
ex2TypeReps (Exists2 (_ :: p a b)) = (typeRep (Proxy :: Proxy a), typeRep (Proxy :: Proxy b))

-- * Type Maps

-- | Associates types @a@ with corresponding values of type @p a@.
type Typemap p = Map TypeRep (Exists p)


-- | Associates types @a@ and @b@ with corresponding values of type @p a b@.
--
-- This map is keyed by @b@ first and @a@ second.
type Typemap2 p = Map TypeRep (Map TypeRep (Exists2 p))


-- | Look up (or traverse over) an 'Typemap' entry for a particular type.
typemapEntry :: Typeable a => proxy a -> Traversal' (Typemap p) (p a)
typemapEntry proxyA = at (typeRep proxyA) . _Just . _Exists


-- | Look up (or traverse over) a 'Typemap2' entry for a particular pair of
-- types.
typemap2Entry :: (Typeable a, Typeable b) => proxy1 a -> proxy2 b -> Traversal' (Typemap2 p) (p a b)
typemap2Entry proxyA proxyB = at (typeRep proxyB) . _Just . at (typeRep proxyA) . _Just . _Exists2


hmapTypemap :: (forall a. Typeable a => p a -> q a) -> Typemap p -> Typemap q
hmapTypemap f = fmap (\(Exists x) -> Exists (f x))


hmapTypemap2 :: (forall a b. (Typeable a, Typeable b) => p a b -> q a b) -> Typemap2 p -> Typemap2 q
hmapTypemap2 f = (fmap . fmap) (\(Exists2 x) -> Exists2 (f x))


-- | Hides the first type parameter of the values in the 'Typemap' to turn it
-- into a 'Typemap2'.
toTypemap2 :: forall a p. Typeable a => Typemap (p a) -> Typemap2 p
toTypemap2 = fmap (\(Exists x) -> Map.singleton (typeRep (Proxy :: Proxy a)) (Exists2 x))

-- * Dictionaries for classes

-- | @'Dict1' p a@ reifies the dictionary for the constraint @p a@.
newtype Dict1 p a = Dict1' (Dict (p a))
makeWrapped ''Dict1

pattern Dict1 :: () => p a => Dict1 p a
pattern Dict1 = Dict1' Dict


-- | @'Dict2' p a b@ reifies the dictionary for the constraint @p a b@.
newtype Dict2 p a b = Dict2' (Dict (p a b))
makeWrapped ''Dict2

pattern Dict2 :: () => p a b => Dict2 p a b
pattern Dict2 = Dict2' Dict


-- | Associates types @a@ with instances of the constraint @p a@.
type Dictmap p = Typemap (Dict1 p)
type Dictmap2 p = Typemap2 (Dict2 p)


-- | Construct a @'Dictmap' p@ from a proof that a list of types each satisfies @p@.
dictmap :: HaveInstances p xs => proxy xs -> Dictmap p
dictmap = Map.fromList . map (\inst -> (exTypeRep inst, inst)) . getInstances


-- | Look up (or traverse over) an 'Dictmap' entry for a particular type.
dictmapEntry :: Typeable a => proxy a -> Traversal' (Dictmap p) (Dict (p a))
dictmapEntry proxyA = typemapEntry proxyA . _Wrapped


-- | Look up (or traverse over) a 'Dictmap2' entry for a particular pair of
-- types.
dictmap2Entry
  :: (Typeable a, Typeable b)
  => proxy1 a -> proxy2 b
  -> Traversal' (Dictmap2 p) (Dict (p a b))
dictmap2Entry proxyA proxyB = typemap2Entry proxyA proxyB . _Wrapped


-- | If the given type @a@ satisfies @p a@ according to the 'Dictmap', do
-- something with the constraint.
--
-- Can also be seen as deferring the constraint @p a@.
withDictmap
  :: Dictmap p
  -> Typeable a
  => proxy a -> (p a => r)
  -> Maybe r
withDictmap dm = \proxy f -> dm ^? dictmapEntry proxy . to (\Dict -> f)


-- | If the given types @a@ and @b@ satisfy @p a b@ according to the 'Dictmap',
-- do something with the constraint.
--
-- Can also be seen as deferring the constraint @p a b@.
withDictmap2
  :: Dictmap2 p
  -> (Typeable a, Typeable b)
  => proxy1 a -> proxy2 b
  -> (p a b => r)
  -> Maybe r
withDictmap2 dm = \proxyA proxyB f -> dm ^? dictmap2Entry proxyA proxyB . to (\Dict -> f)


-- | Find all of the entries of the 'Dictmap2' of the shape @p a b@ for some
-- fixed b, and act on each of them. Return the list of results.
withDictmap2'
  :: Dictmap2 p
  -> (Typeable b)
  => proxy b
  -> (forall a. (Typeable a, p a b) => Proxy a -> r)
  -> [r]
withDictmap2' dm = \(proxy :: proxy b) f -> do
  bInstances <- dm ^.. at (typeRep proxy) . _Just

  (_, Exists2 (Dict2 :: Dict2 p a b')) <- Map.toList bInstances

  Refl :: b :~: b' <- eqT ^.. _Just

  return (f (Proxy :: Proxy a))

-- | Hides the first type parameter of the values in the 'Dictmap' to turn it
-- into a 'Dictmap2'.
toDictmap2 :: forall a p. Typeable a => Dictmap (p a) -> Dictmap2 p
toDictmap2 = fmap (\(Exists (Dict1 :: Dict1 (p a) b)) ->
                     Map.singleton (typeRep (Proxy :: Proxy a)) (Exists2 (Dict2 :: Dict2 p a b)))

-- * Constraints over each type in a list

-- | An instance @'HaveInstances' p as@ for a type class @p@ and a list of types
-- @as@ means that each type in @as@ satisfies @p@, and we can get a list of the
-- reified @p@ instances for all of those types.
--
-- Useful for reducing boilerplate in producing lists of @'SomeInstance' p@.
class HaveInstances (p :: k -> Constraint) (as :: [k]) where
  getInstances :: proxy as -> [Exists (Dict1 p)]
  getInstances types =
    withInstances (Proxy :: Proxy p) types
      (\(_ :: Proxy b) -> Exists (Dict1 :: Dict1 p b))

  withInstances
    :: proxy1 p -> proxy2 as
    -> (forall b. (Typeable b, p b) => Proxy b -> r)
    -> [r]
  withInstances (_ :: proxy p) types f =
    do Exists (Dict1 :: Dict1 p b) <- getInstances types
       return (f (Proxy :: Proxy b))


instance HaveInstances p '[] where
  getInstances _ = []

instance (Typeable a, p a, HaveInstances p as) => HaveInstances p (a : as) where
  getInstances _ =
    let x :: Exists (Dict1 p)
        x = Exists (Dict1 :: Dict1 p a)

        xs :: [Exists (Dict1 p)]
        xs = getInstances (Proxy :: Proxy as)
    in x : xs
