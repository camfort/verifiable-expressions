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

module Language.Expression.Dict where

import           Data.Constraint (Constraint)
import           Data.Typeable

import           Control.Lens    hiding ((.>))
import           Data.Map        (Map)
import qualified Data.Map        as Map

import           Data.SBV hiding ((#))

--------------------------------------------------------------------------------
--  Dictionaries for standard type classes
--------------------------------------------------------------------------------

data BooleanDict a =
  BooleanDict
  { _dictFromBool :: Bool -> a
  , _dictNot      :: a -> a
  , _dictAnd      :: a -> a -> a
  , _dictOr       :: a -> a -> a
  , _dictImpl     :: a -> a -> a
  , _dictEquiv    :: a -> a -> a
  }

makeLenses ''BooleanDict

data EqDict b a =
  EqDict
  { _dictEq       :: a -> a -> b
  , _dictNeq      :: a -> a -> b
  }

makeLenses ''EqDict

data OrdDict b a =
  OrdDict
  { _dictLt       :: a -> a -> b
  , _dictLe       :: a -> a -> b
  , _dictGt       :: a -> a -> b
  , _dictGe       :: a -> a -> b
  }

makeLenses ''OrdDict

data NumDict a =
  NumDict
  { _dictAdd      :: a -> a -> a
  , _dictMul      :: a -> a -> a
  , _dictSub      :: a -> a -> a
  }

makeLenses ''NumDict

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

eqDict :: Eq a => EqDict Bool a
eqDict =
  EqDict
  { _dictEq = (==)
  , _dictNeq = (/=)
  }

ordDict :: Ord a => OrdDict Bool a
ordDict =
  OrdDict
  { _dictLt = (<)
  , _dictLe = (<=)
  , _dictGt = (>)
  , _dictGe = (>=)
  }

numDict :: Num a => NumDict a
numDict =
  NumDict
  { _dictAdd = (+)
  , _dictMul = (*)
  , _dictSub = (-)
  }

eqSymbolicDict :: EqSymbolic a => EqDict SBool a
eqSymbolicDict =
  EqDict
  { _dictEq = (.==)
  , _dictNeq = (./=)
  }

ordSymbolicDict :: OrdSymbolic a => OrdDict SBool a
ordSymbolicDict =
  OrdDict
  { _dictLt = (.<)
  , _dictLe = (.<=)
  , _dictGt = (.>)
  , _dictGe = (.>=)
  }

--------------------------------------------------------------------------------
--  Things that have dictionaries
--------------------------------------------------------------------------------

class HasDicts dict s where
  dicts :: Lens' s (Dictmap dict)

  dictFor :: Typeable a => proxy a -> Traversal' s (dict a)
  dictFor proxyA = dicts . dictmapEntry proxyA

class HasDicts2 dict s where
  dicts2 :: Lens' s (Dictmap2 dict)

  dict2For :: (Typeable a, Typeable b) => proxy1 a -> proxy2 b -> Traversal' s (dict a b)
  dict2For proxyA proxyB = dicts2 . dictmap2Entry proxyA proxyB

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

type Dictmap dict = Map TypeRep (Exists dict)

type Dictmap2 dict = Map (TypeRep, TypeRep) (Exists2 dict)


dictmapEntry :: Typeable a => proxy a -> Traversal' (Dictmap dict) (dict a)
dictmapEntry proxyA = at (typeRep proxyA) . _Just . _Exists

dictmap2Entry :: (Typeable a, Typeable b) => proxy1 a -> proxy2 b -> Traversal' (Dictmap2 dict) (dict a b)
dictmap2Entry proxyA proxyB = at (typeRep proxyA, typeRep proxyB) . _Just . _Exists2


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


makeDictmap2 :: forall a dict. (Typeable a) => Dictmap (dict a) -> Dictmap2 dict
makeDictmap2 =
  let arep = typeRep (Proxy :: Proxy a)
  in Map.fromList
   . map (\(brep, entry) -> ((arep, brep), toExists2 entry))
   . Map.toList

--------------------------------------------------------------------------------
--  Constraint Machinery
--------------------------------------------------------------------------------

data Exists dict where
  Exists :: Typeable a => dict a -> Exists dict

data Exists2 dict where
  Exists2 :: (Typeable a, Typeable b) => dict a b -> Exists2 dict

_Exists :: forall a b dict. (Typeable a, Typeable b) => Prism (Exists dict) (Exists dict) (dict a) (dict b)
_Exists = prism Exists extract
  where
    extract (Exists d) =
      maybe (Left (Exists d)) Right $ gcast d

_Exists2
  :: forall a b c d dict.
     (Typeable a, Typeable b, Typeable c, Typeable d)
  => Prism (Exists2 dict) (Exists2 dict) (dict a b) (dict c d)
_Exists2 = prism Exists2 extract
  where
    extract (Exists2 d) =
      maybe (Left (Exists2 d)) Right $ gcast2' d

toExists2 :: (Typeable a) => Exists (dict a) -> Exists2 dict
toExists2 (Exists d) = Exists2 d


gcast2' :: forall a b c d p. (Typeable a, Typeable b, Typeable c, Typeable d) => p a b -> Maybe (p c d)
gcast2' x
  | Just Refl <- eqT :: Maybe (a :~: c)
  , Just Refl <- eqT :: Maybe (b :~: d) = Just x
  | otherwise = Nothing

data SomeInstance p where
  SomeInstance :: (Typeable a, p a) => Proxy a -> SomeInstance p

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
