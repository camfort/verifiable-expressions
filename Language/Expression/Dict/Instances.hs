{-# LANGUAGE DataKinds #-}

module Language.Expression.Dict.Instances where

import           Data.Typeable                      (Proxy (..))

import           Data.SBV                           hiding (( # ))

import           Language.Expression.Dict

--------------------------------------------------------------------------------
--  Boolean
--------------------------------------------------------------------------------

standardBooleanInstances :: Dictmap BooleanDict
standardBooleanInstances =
  makeDictmap (Proxy :: Proxy Boolean) booleanDict
  (Proxy :: Proxy
    '[ Bool
     , SBool
     ])

--------------------------------------------------------------------------------
--  Ord
--------------------------------------------------------------------------------

standardOrdInstances :: Dictmap2 OrdDict
standardOrdInstances =
  makeDictmap2 boolOrdInstances `mappend`
  makeDictmap2 sBoolOrdInstances


boolOrdInstances :: Dictmap (OrdDict Bool)
boolOrdInstances =
  makeDictmap (Proxy :: Proxy Ord) ordDict
  (Proxy :: Proxy
    '[ Integer
     , Float
     , Double
     , Bool
     , Int
     , Int8
     , Int16
     , Int32
     , Int64
     , Word
     , Word8
     , Word16
     , Word32
     , Word64
     , AlgReal
     ])

sBoolOrdInstances :: Dictmap (OrdDict SBool)
sBoolOrdInstances =
  makeDictmap (Proxy :: Proxy OrdSymbolic) ordSymbolicDict
  (Proxy :: Proxy
    '[ SInteger
     , SFloat
     , SDouble
     , SBool
     , SInt8
     , SInt16
     , SInt32
     , SInt64
     , SWord8
     , SWord16
     , SWord32
     , SWord64
     , SReal
     ])

--------------------------------------------------------------------------------
--  Eq
--------------------------------------------------------------------------------

standardEqInstances :: Dictmap2 EqDict
standardEqInstances =
  makeDictmap2 boolEqInstances `mappend`
  makeDictmap2 sBoolEqInstances

boolEqInstances :: Dictmap (EqDict Bool)
boolEqInstances =
  makeDictmap (Proxy :: Proxy Eq) eqDict
  (Proxy :: Proxy
    '[ Integer
     , Float
     , Double
     , Bool
     , Int
     , Int8
     , Int16
     , Int32
     , Int64
     , Word
     , Word8
     , Word16
     , Word32
     , Word64
     , AlgReal
     ])

sBoolEqInstances :: Dictmap (EqDict SBool)
sBoolEqInstances =
  makeDictmap (Proxy :: Proxy EqSymbolic) eqSymbolicDict
  (Proxy :: Proxy
    '[ SInteger
     , SFloat
     , SDouble
     , SBool
     , SInt8
     , SInt16
     , SInt32
     , SInt64
     , SWord8
     , SWord16
     , SWord32
     , SWord64
     , SReal
     ])

--------------------------------------------------------------------------------
--  Num
--------------------------------------------------------------------------------

standardNumInstances :: Dictmap NumDict
standardNumInstances =
  makeDictmap (Proxy :: Proxy Num) numDict
  (Proxy :: Proxy
    '[ Integer
     , Float
     , Double
     , Int
     , Int8
     , Int16
     , Int32
     , Int64
     , Word
     , Word8
     , Word16
     , Word32
     , Word64
     , SInteger
     , SFloat
     , SDouble
     , SInt8
     , SInt16
     , SInt32
     , SInt64
     , SWord8
     , SWord16
     , SWord32
     , SWord64
     , AlgReal
     , SReal
     ])

