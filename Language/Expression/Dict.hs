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

import           Data.Typeable

import qualified Data.Map                        as Map

import           Control.Lens                    hiding ((.>))

import           Data.SBV                        hiding (( # ))

import           Language.Expression.Constraints

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
  { _dictEq  :: a -> a -> b
  , _dictNeq :: a -> a -> b
  }

-- | A reified 2-dictionary for the 'Ord' class that generalizes the type of
-- boolean.
data OrdDict b a =
  OrdDict
  { _dictLt :: a -> a -> b
  , _dictLe :: a -> a -> b
  , _dictGt :: a -> a -> b
  , _dictGe :: a -> a -> b
  }

-- | A reified dictionary for the 'Num' class.
data NumDict a =
  NumDict
  { _dictAdd :: a -> a -> a
  , _dictMul :: a -> a -> a
  , _typemapub :: a -> a -> a
  }

-- | A dictionary entry for types that can be coerced into each other.
data CoerceDict a b =
  CoerceDict
  { _dictCoerce :: a -> b
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
  , _typemapub = (-)
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
makeLenses ''CoerceDict


-- * Combinators

typemapFromClass :: (HaveInstances p xs) => proxy1 p -> (forall a. p a => k a) -> proxy2 xs -> Typemap k
typemapFromClass (_ :: proxy1 p) f proxyXs =
  let dm = dictmap proxyXs :: Dictmap p
  in hmapTypemap (\Dict1 -> f) dm


typemap2FromList :: [Exists2 p] -> Typemap2 p
typemap2FromList xs =
  let entries = [(trB, [(trA, x)]) | x <- xs, let (trA, trB) = ex2TypeReps x]
      byB = Map.fromListWith (++) entries
  in fmap Map.fromList byB


-- * Dictionary lookup type classes

-- | The class of environments which contain 'Typemap's for the particular
-- dictionary @dict@.
class HasTypemap dict s where
  -- | Get the 'Typemap' from the environment.
  typemap :: Lens' s (Typemap dict)

  -- | Look up a dictionary for a particular type in the dictionary provided by
  -- the environment.
  instanceFor :: Typeable a => proxy a -> Traversal' s (dict a)
  instanceFor proxyA = typemap . typemapEntry proxyA

-- | The class of environments which contain 'Typemap2's for the particular
-- 2-dictionary @dict@.
class HasTypemap2 dict s where
  -- | Get the 'Typemap2' from the environment.
  typemap2 :: Lens' s (Typemap2 dict)

  -- | Look up a dictionary for a particular pair of types in the 2-dictionary
  -- provided by the environment.
  instance2For :: (Typeable a, Typeable b) => proxy1 a -> proxy2 b -> Traversal' s (dict a b)
  instance2For proxyA proxyB = typemap2 . typemap2Entry proxyA proxyB
