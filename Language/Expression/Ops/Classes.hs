{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

{-|

Type classes used to constrain the types that the standard operators can work
with.

-}
module Language.Expression.Ops.Classes where

import           Data.Int
import           Data.Typeable (Typeable)
import           Data.Word

import           Data.SBV      (AlgReal)

--------------------------------------------------------------------------------
--  SymValue
--------------------------------------------------------------------------------

-- | A type that can be represented by symbolic values.
class (Typeable a, Eq a) => SymValue a where
  prettyValue :: a -> String
  prettyValue = prettyValuePrec 0

  prettyValuePrec :: Int -> a -> String

  default prettyValuePrec :: Show a => Int -> a -> String
  prettyValuePrec p x = showsPrec p x ""

instance SymValue Bool
instance SymValue Integer
instance SymValue Float
instance SymValue Double
instance SymValue AlgReal
instance SymValue Word8
instance SymValue Word16
instance SymValue Word32
instance SymValue Word64
instance SymValue Word
instance SymValue Int8
instance SymValue Int16
instance SymValue Int32
instance SymValue Int64
instance SymValue Int

