{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

{-|

Type classes used to constrain the types that the standard operators can work
with.

-}
module Language.Expression.Classes where

import           Data.Int
import           Data.Typeable (Typeable)
import           Data.Word

import           Data.SBV      (AlgReal, SBV)
import qualified Data.SBV      as S

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

--------------------------------------------------------------------------------
--  SymLit
--------------------------------------------------------------------------------

-- TODO: Remove this class, use dictionaries instead

class SymValue a => SymLit a where
  toSbv :: a -> SBV a

instance SymLit Bool where toSbv = S.fromBool
instance SymLit Integer where toSbv = fromIntegral
instance SymLit Int8 where toSbv = fromIntegral
instance SymLit Int16 where toSbv = fromIntegral
instance SymLit Int32 where toSbv = fromIntegral
instance SymLit Int64 where toSbv = fromIntegral
instance SymLit Word8 where toSbv = fromIntegral
instance SymLit Word16 where toSbv = fromIntegral
instance SymLit Word32 where toSbv = fromIntegral
instance SymLit Word64 where toSbv = fromIntegral

-- TODO: Implement these
instance SymLit Float where toSbv = error "Float to SBV"
instance SymLit Double where toSbv = error "Double to SBV"
instance SymLit AlgReal where toSbv = error "AlgReal to SBV"

--------------------------------------------------------------------------------
--  SymBool
--------------------------------------------------------------------------------

-- | Generalized booleans.
class SymValue b => SymBool b where
  symFromBool :: Bool -> b

  symAnd :: b -> b -> b
  symNot :: b -> b

  symOr :: b -> b -> b
  symOr a b = symNot ((symNot a) `symAnd` (symNot b))

  symImpl :: b -> b -> b
  symImpl x y = (symNot x) `symOr` y

  symEquiv :: b -> b -> b
  symEquiv x y = (x `symImpl` y) `symAnd` (y `symImpl` x)

instance SymBool Bool where
  symFromBool = id
  symAnd = (&&)
  symOr = (||)
  symNot = not

--------------------------------------------------------------------------------
--  SymEq
--------------------------------------------------------------------------------

-- | Generalized equality which can return results in the land of generalized
-- booleans.
class (SymValue a, SymBool b) => SymEq b a where
  symEq :: a -> a -> b

  symNeq :: a -> a -> b
  x `symNeq` y = symNot (x `symEq` y)

instance (Eq a, SymValue a) => SymEq Bool a where
  symEq = (==)
  symNeq = (/=)

--------------------------------------------------------------------------------
--  SymOrd
--------------------------------------------------------------------------------

-- | Generalized ordering which can return results in the land of generalized
-- booleans.
class (SymEq b a, SymBool b) => SymOrd b a where
  symLt :: a -> a -> b

  symLe :: a -> a -> b
  symLe x y = (x `symLt` y) `symOr` (x `symEq` y)

  symGt :: a -> a -> b
  symGt x y = symNot (symLe x y)

  symGe :: a -> a -> b
  symGe x y = symNot (symLt x y)

instance (Ord a, SymValue a) => SymOrd Bool a where
  symLt = (<)
  symLe = (<=)
  symGt = (>)
  symGe = (>=)

--------------------------------------------------------------------------------
--  SymNum
--------------------------------------------------------------------------------

-- | Generalized numbers that don't have to have all the extra cruft that 'Num'
-- forces us to have.
class (SymValue a) => SymNum a where
  symAdd :: a -> a -> a
  symSub :: a -> a -> a
  symMul :: a -> a -> a

  default symAdd :: (Num a) => a -> a -> a
  symAdd = (+)

  default symSub :: (Num a) => a -> a -> a
  symSub = (-)

  default symMul :: (Num a) => a -> a -> a
  symMul = (*)

instance (SymValue a, Num a) => SymNum a

--------------------------------------------------------------------------------
--  SymCoercible
--------------------------------------------------------------------------------

-- | Values that can be coerced into another type.
class (SymValue a, SymValue b) => SymCoercible a b where
  symCoerce :: a -> b

-- TODO: SymCoercible instances

instance SymCoercible Integer Int where symCoerce = fromInteger
instance SymCoercible Integer Int8 where symCoerce = fromInteger
instance SymCoercible Integer Int16 where symCoerce = fromInteger
instance SymCoercible Integer Int32 where symCoerce = fromInteger
instance SymCoercible Integer Int64 where symCoerce = fromInteger

instance SymCoercible Integer Word where symCoerce = fromInteger
instance SymCoercible Integer Word8 where symCoerce = fromInteger
instance SymCoercible Integer Word16 where symCoerce = fromInteger
instance SymCoercible Integer Word32 where symCoerce = fromInteger
instance SymCoercible Integer Word64 where symCoerce = fromInteger

instance SymCoercible Integer Float where symCoerce = fromInteger
instance SymCoercible Integer Double where symCoerce = fromInteger

instance SymCoercible Float Double where symCoerce = fromRational . toRational
instance SymCoercible Double Float where symCoerce = fromRational . toRational
