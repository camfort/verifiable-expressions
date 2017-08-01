{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

{-|

Reified dictionaries of operations corresponding to various type classes.

These are used when evaluating operators in special contexts such as 'SBV'. Since
operators such as 'OrdOp' contain existential types, it becomes necessary to
resort to dynamic (run-time) instance selection to decide what to do when
evaluating them in special contexts. The other option would be to hard-code a
list of contexts in which they can be evaluated. However, if we did that, then
whenever you want to evaluate an ordering operation in a new context, you'd
either have to fork this library to add it, or define your own new ordering
operation. Therefore, in the name of modularity, we use the dynamic approach
instead.

See "Language.Expression.Dict.Instances" for some concrete dictionary maps.

See also "Language.Expression.SBV" which uses this infrastructure to evaluate
expressions.

-}
module Language.Expression.Dict where

import           Data.Constraint (Constraint)
import           Data.Typeable

import           Control.Lens    hiding ((.>))
import           Data.Map        (Map)
import qualified Data.Map        as Map

import           Data.SBV hiding ((#))

-- * Dictionaries for standard type classes

-- | A reified dictionary for the 'Boolean' class (from "Data.SBV").
data BooleanDict a =
  BooleanDict
  { _dictFromBool :: Bool -> a
  , _dictNot      :: a -> a
  , _dictAnd      :: a -> a -> a
  , _dictOr       :: a -> a -> a
  , _dictImpl     :: a -> a -> a
  , _dictEquiv    :: a -> a -> a
  }

-- | A reified 2-dictionary for the 'Eq' class that generalizes the type of
-- boolean.
data EqDict b a =
  EqDict
  { _dictEq       :: a -> a -> b
  , _dictNeq      :: a -> a -> b
  }

-- | A reified 2-dictionary for the 'Ord' class that generalizes the type of
-- boolean.
data OrdDict b a =
  OrdDict
  { _dictLt       :: a -> a -> b
  , _dictLe       :: a -> a -> b
  , _dictGt       :: a -> a -> b
  , _dictGe       :: a -> a -> b
  }

-- | A reified dictionary for the 'Num' class.
data NumDict a =
  NumDict
  { _dictAdd      :: a -> a -> a
  , _dictMul      :: a -> a -> a
  , _dictSub      :: a -> a -> a
  }

-- * Constructing dictionaries

-- | Create a 'BooleanDict' from a 'Boolean' instance.
booleanDict :: Boolean a => BooleanDict a
booleanDict =
  BooleanDict
  { _dictFromBool = fromBool
  , _dictNot = bnot
  , _dictAnd = (&&&)
  , _dictOr = (|||)
  , _dictImpl = (==>)
  , _dictEquiv = (<=>)
  }

-- | Create an 'EqDict' from an 'Eq' instance.
eqDict :: Eq a => EqDict Bool a
eqDict =
  EqDict
  { _dictEq = (==)
  , _dictNeq = (/=)
  }

-- | Create an 'OrdDict' from an 'Ord' instance.
ordDict :: Ord a => OrdDict Bool a
ordDict =
  OrdDict
  { _dictLt = (<)
  , _dictLe = (<=)
  , _dictGt = (>)
  , _dictGe = (>=)
  }

-- | Create a 'NumDict' from a 'Num' instace.
numDict :: Num a => NumDict a
numDict =
  NumDict
  { _dictAdd = (+)
  , _dictMul = (*)
  , _dictSub = (-)
  }

-- | Create an 'EqDict' from an 'EqSymbolic' instance.
eqSymbolicDict :: EqSymbolic a => EqDict SBool a
eqSymbolicDict =
  EqDict
  { _dictEq = (.==)
  , _dictNeq = (./=)
  }

-- | Create an 'OrdDict' from an 'OrdSymbolic' instance.
ordSymbolicDict :: OrdSymbolic a => OrdDict SBool a
ordSymbolicDict =
  OrdDict
  { _dictLt = (.<)
  , _dictLe = (.<=)
  , _dictGt = (.>)
  , _dictGe = (.>=)
  }

-- * Lenses for dictionary types

makeLenses ''BooleanDict
makeLenses ''EqDict
makeLenses ''OrdDict
makeLenses ''NumDict

-- * Maps of dictionaries

-- | A map of dictionaries of the particular type @dict@. Associates types with
-- dictionaries for that type.
type Dictmap dict = Map TypeRep (Exists dict)

-- | A map of 2-dictionaries of the particular type @dict@. Associates pairs of
-- types with 2-dictionaries for those types.
type Dictmap2 dict = Map (TypeRep, TypeRep) (Exists2 dict)


-- | Look up (or traverse over) a 'Dictmap' entry for a particular type.
dictmapEntry :: Typeable a => proxy a -> Traversal' (Dictmap dict) (dict a)
dictmapEntry proxyA = at (typeRep proxyA) . _Just . _Exists

-- | Look up (or traverse over) a 'Dictmap2' entry for a particular pair of
-- types.
dictmap2Entry :: (Typeable a, Typeable b) => proxy1 a -> proxy2 b -> Traversal' (Dictmap2 dict) (dict a b)
dictmap2Entry proxyA proxyB = at (typeRep proxyA, typeRep proxyB) . _Just . _Exists2


-- | Given a function to construct a dictionary from a constraint @p@, and a
-- list of types @as@ which each satisfy @p a@, get a list of all the
-- dictionaries for those types.
makeDictList
  :: forall p as dict proxy1 proxy2.
     HaveInstances p as
  => proxy1 p
  -> (forall a. p a => dict a)
  -> proxy2 as
  -> [Exists dict]
makeDictList _ makeDict proxyAs = map makeExists (getInstances proxyAs)
  where
    makeExists :: SomeInstance p -> Exists dict
    makeExists (SomeInstance (_ :: Proxy b)) = Exists (makeDict :: dict b)

-- | Given a function to construct a dictionary from a constraint @p@, and a
-- list of types @as@ which each satisfy @p a@, get a 'Dictmap' of all the
-- dictionaries for those types.
makeDictmap
  :: forall p as dict proxy1 proxy2.
     HaveInstances p as
  => proxy1 p
  -> (forall a. p a => dict a)
  -> proxy2 as
  -> Dictmap dict
makeDictmap proxyP makeDict proxyAs = listToMap (makeDictList proxyP makeDict proxyAs)
  where
    listToMap = Map.fromList . map (\e -> (exTypeRep e, e))
    exTypeRep (Exists (_ :: dict a)) = typeRep (Proxy :: Proxy a)

-- | Turn a 'Dictmap' into a 'Dictmap2'.
makeDictmap2 :: forall a dict. (Typeable a) => Dictmap (dict a) -> Dictmap2 dict
makeDictmap2 =
  let arep = typeRep (Proxy :: Proxy a)
  in Map.fromList
   . map (\(brep, entry) -> ((arep, brep), toExists2 entry))
   . Map.toList

-- * Dictionary lookup type classes

-- | The class of environments which contain 'Dictmap's for the particular
-- dictionary @dict@.
class HasDicts dict s where
  -- | Get the 'Dictmap' from the environment.
  dicts :: Lens' s (Dictmap dict)

  -- | Look up a dictionary for a particular type in the dictionary provided by
  -- the environment.
  dictFor :: Typeable a => proxy a -> Traversal' s (dict a)
  dictFor proxyA = dicts . dictmapEntry proxyA

-- | The class of environments which contain 'Dictmap2's for the particular
-- 2-dictionary @dict@.
class HasDicts2 dict s where
  -- | Get the 'Dictmap2' from the environment.
  dicts2 :: Lens' s (Dictmap2 dict)

  -- | Look up a dictionary for a particular pair of types in the 2-dictionary
  -- provided by the environment.
  dict2For :: (Typeable a, Typeable b) => proxy1 a -> proxy2 b -> Traversal' s (dict a b)
  dict2For proxyA proxyB = dicts2 . dictmap2Entry proxyA proxyB

-- * Constraint machinery

-- | An existential dictionary, i.e. a dictionary for some hidden type.
data Exists dict where
  Exists :: Typeable a => dict a -> Exists dict

-- | An existential 2-dictionary, i.e. a 2-dictionary for a pair of hidden types.
data Exists2 dict where
  Exists2 :: (Typeable a, Typeable b) => dict a b -> Exists2 dict

-- | Project a dictionary for a particular type out of an existential. Fails
-- whenever the requested type doesn't match the type that's actually inside the
-- existential.
_Exists :: forall a b dict. (Typeable a, Typeable b) => Prism (Exists dict) (Exists dict) (dict a) (dict b)
_Exists = prism Exists extract
  where
    extract (Exists d) =
      maybe (Left (Exists d)) Right $ gcast d

-- | Project a 2-dictionary for a particular type out of an existential. Fails
-- whenever the requested types don't match the types that are actually inside
-- the existential.
_Exists2
  :: forall a b c d dict.
     (Typeable a, Typeable b, Typeable c, Typeable d)
  => Prism (Exists2 dict) (Exists2 dict) (dict a b) (dict c d)
_Exists2 = prism Exists2 extract
  where
    extract (Exists2 d) =
      maybe (Left (Exists2 d)) Right $ gcast2' d

-- | Convert an existential dictionary (with a remaining rigid type argument)
-- into an existential 2-dictionary.
toExists2 :: (Typeable a) => Exists (dict a) -> Exists2 dict
toExists2 (Exists d) = Exists2 d


-- | Like 'gcast' from "Data.Typeable", but casts the two type arguments of a
-- binary type constructor.
gcast2' :: forall a b c d p. (Typeable a, Typeable b, Typeable c, Typeable d) => p a b -> Maybe (p c d)
gcast2' x
  | Just Refl <- eqT :: Maybe (a :~: c)
  , Just Refl <- eqT :: Maybe (b :~: d) = Just x
  | otherwise = Nothing

-- | An existential which asserts that we have an instance of the class @p@ for
-- some type, but we are hiding which type the instance is for.
data SomeInstance p where
  SomeInstance :: (Typeable a, p a) => Proxy a -> SomeInstance p

-- | An instance @'HaveInstances' p as@ for a type class @p@ and a list of types
-- @as@ means that each type in @as@ satisfies @p@, and we can get a list of the
-- reified @p@ instances for all of those types.
--
-- Useful for reducing boilerplate in producing lists of @'SomeInstance' p@.
class HaveInstances (p :: k -> Constraint) (as :: [k]) where
  getInstances :: proxy as -> [SomeInstance p]

instance HaveInstances p '[] where
  getInstances _ = []

instance (Typeable a, p a, HaveInstances p as) => HaveInstances p (a : as) where
  getInstances _ =
    let x :: SomeInstance p
        x = SomeInstance (Proxy :: Proxy a)

        xs :: [SomeInstance p]
        xs = getInstances (Proxy :: Proxy as)

    in x : xs
