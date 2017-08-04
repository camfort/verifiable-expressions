{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|

Default examples of 'Typemap's and 'Typemap2's for standard type classes.

-}
module Language.Expression.Dict.Instances where

import           Data.Typeable                      (Proxy (..), eqT, (:~:)(..))

import           Data.SBV                           hiding (( # ))

import           Language.Expression.Constraints
import           Language.Expression.Dict
import           Language.Expression.Unknown

--------------------------------------------------------------------------------
--  Boolean
--------------------------------------------------------------------------------

-- | 'BooleanDict's for 'Bool' and 'SBool'.
standardBooleanInstances :: Typemap BooleanDict
standardBooleanInstances =
  typemapFromClass (Proxy :: Proxy Boolean) booleanDict
  (Proxy :: Proxy
    '[ Bool
     , SBool
     ])

--------------------------------------------------------------------------------
--  Ord
--------------------------------------------------------------------------------

{-|
The union of 'boolOrdInstances' and 'sBoolOrdInstances', with the boolean types
abstracted away.
-}
standardOrdInstances :: Typemap2 OrdDict
standardOrdInstances =
  toTypemap2 boolOrdInstances `mappend`
  toTypemap2 sBoolOrdInstances

{-|
@'OrdDict' 'Bool'@ for:

'Integer'
'Float'
'Double'
'Bool'
'Int'
'Int8'
'Int16'
'Int32'
'Int64'
'Word'
'Word8'
'Word16'
'Word32'
'Word64'
'AlgReal'
-}
boolOrdInstances :: Typemap (OrdDict Bool)
boolOrdInstances =
  typemapFromClass (Proxy :: Proxy Ord) ordDict
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

{-|
@'OrdDict' 'SBool'@ for:

'SInteger'
'SFloat'
'SDouble'
'SBool'
'SInt8'
'SInt16'
'SInt32'
'SInt64'
'SWord8'
'SWord16'
'SWord32'
'SWord64'
'SReal'
-}
sBoolOrdInstances :: Typemap (OrdDict SBool)
sBoolOrdInstances =
  typemapFromClass (Proxy :: Proxy OrdSymbolic) ordSymbolicDict
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

{-|
The union of 'boolEqInstances' and 'sBoolEqInstances', with the boolean types
abstracted away.
-}
standardEqInstances :: Typemap2 EqDict
standardEqInstances =
  toTypemap2 boolEqInstances `mappend`
  toTypemap2 sBoolEqInstances

{-|
@'EqDict' 'Bool'@ for:

'Integer'
'Float'
'Double'
'Bool'
'Int'
'Int8'
'Int16'
'Int32'
'Int64'
'Word'
'Word8'
'Word16'
'Word32'
'Word64'
'AlgReal'
-}
boolEqInstances :: Typemap (EqDict Bool)
boolEqInstances =
  typemapFromClass (Proxy :: Proxy Eq) eqDict
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

{-|
@'EqDict' 'SBool'@ for:

'SInteger'
'SFloat'
'SDouble'
'SBool'
'SInt8'
'SInt16'
'SInt32'
'SInt64'
'SWord8'
'SWord16'
'SWord32'
'SWord64'
'SReal'
-}
sBoolEqInstances :: Typemap (EqDict SBool)
sBoolEqInstances =
  typemapFromClass (Proxy :: Proxy EqSymbolic) eqSymbolicDict
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

{-|
'NumDict's for:

'Integer'
'Float'
'Double'
'Int'
'Int8'
'Int16'
'Int32'
'Int64'
'Word'
'Word8'
'Word16'
'Word32'
'Word64'
'SInteger'
'SFloat'
'SDouble'
'SInt8'
'SInt16'
'SInt32'
'SInt64'
'SWord8'
'SWord16'
'SWord32'
'SWord64'
'AlgReal'
'SReal'
-}
standardNumInstances :: Typemap NumDict
standardNumInstances =
  typemapFromClass (Proxy :: Proxy Num) numDict
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

--------------------------------------------------------------------------------
--  Coercion
--------------------------------------------------------------------------------

-- TODO: Add 'AlgReal' into the mix.
-- TODO: Coercions between symbolic SBV values.

{-|

'CoerceDict's. The integral types covered are 'Int', 'Word', 'Integer' and each
@Int{8,16,32,64}@ and @Word{8,16,32,64}@. The floating point types covered are
'Float' and 'Double'. Coercions exist:

- from each integral to each floating point type;
- between each pair of integral types;
- from 'Double' to 'Float';
- from 'Unknown' to each other mentioned type.
-}
standardCoerceInstances :: Typemap2 CoerceDict
standardCoerceInstances =
  typemap2FromList
    (
    -- Converting between floating point types, and from integers to floating point
       [doubleToFloat, integerToFloat, integerToDouble]
    -- Converting from each integral type to 'Integer'
    ++ fromIntegrals
    -- Converting from 'Integer' to each integral type
    ++ toIntegrals
    -- Converting between each pair of integral types (TODO: may lose precision)
    ++ betweenIntegrals
    -- Converting from each integral type to 'Double'
    ++ (integerToDouble ..* fromIntegrals)
    -- Converting from each integral type to 'Float'
    ++ (integerToFloat ..* fromIntegrals)
    -- Converting 'Unknown' to anything
    ++ fromUnknowns
    )
  where
    betweenIntegrals = do
      to <- toIntegrals
      to ..* fromIntegrals

    fromUnknowns :: [Exists2 CoerceDict]
    fromUnknowns =
      [ Exists2 (fromUnknown' :: CoerceDict Unknown Integer)
      , Exists2 (fromUnknown' :: CoerceDict Unknown Float)
      , Exists2 (fromUnknown' :: CoerceDict Unknown Double)
      , Exists2 (fromUnknown' :: CoerceDict Unknown Int)
      , Exists2 (fromUnknown' :: CoerceDict Unknown Int8)
      , Exists2 (fromUnknown' :: CoerceDict Unknown Int16)
      , Exists2 (fromUnknown' :: CoerceDict Unknown Int32)
      , Exists2 (fromUnknown' :: CoerceDict Unknown Int64)
      , Exists2 (fromUnknown' :: CoerceDict Unknown Word)
      , Exists2 (fromUnknown' :: CoerceDict Unknown Word8)
      , Exists2 (fromUnknown' :: CoerceDict Unknown Word16)
      , Exists2 (fromUnknown' :: CoerceDict Unknown Word32)
      , Exists2 (fromUnknown' :: CoerceDict Unknown Word64)
      ]

    fromIntegrals :: [Exists2 CoerceDict]
    fromIntegrals =
      [ Exists2 (fromIntegral' :: CoerceDict Int Integer)
      , Exists2 (fromIntegral' :: CoerceDict Int8 Integer)
      , Exists2 (fromIntegral' :: CoerceDict Int16 Integer)
      , Exists2 (fromIntegral' :: CoerceDict Int32 Integer)
      , Exists2 (fromIntegral' :: CoerceDict Int64 Integer)
      , Exists2 (fromIntegral' :: CoerceDict Word Integer)
      , Exists2 (fromIntegral' :: CoerceDict Word8 Integer)
      , Exists2 (fromIntegral' :: CoerceDict Word16 Integer)
      , Exists2 (fromIntegral' :: CoerceDict Word32 Integer)
      , Exists2 (fromIntegral' :: CoerceDict Word64 Integer)
      ]

    toIntegrals :: [Exists2 CoerceDict]
    toIntegrals =
      [ Exists2 (fromIntegral' :: CoerceDict Integer Int)
      , Exists2 (fromIntegral' :: CoerceDict Integer Int8)
      , Exists2 (fromIntegral' :: CoerceDict Integer Int16)
      , Exists2 (fromIntegral' :: CoerceDict Integer Int32)
      , Exists2 (fromIntegral' :: CoerceDict Integer Int64)
      , Exists2 (fromIntegral' :: CoerceDict Integer Word)
      , Exists2 (fromIntegral' :: CoerceDict Integer Word8)
      , Exists2 (fromIntegral' :: CoerceDict Integer Word16)
      , Exists2 (fromIntegral' :: CoerceDict Integer Word32)
      , Exists2 (fromIntegral' :: CoerceDict Integer Word64)
      ]

    integerToDouble :: Exists2 CoerceDict
    integerToDouble = Exists2 $ CoerceDict (fromIntegral :: Integer -> Double)

    integerToFloat :: Exists2 CoerceDict
    integerToFloat = Exists2 $ CoerceDict (fromIntegral :: Integer -> Float)

    doubleToFloat :: Exists2 CoerceDict
    doubleToFloat = Exists2 $ CoerceDict (fromRational . toRational :: Double -> Float)

    -- Dynamically typed coercion composition
    (.*) :: Exists2 CoerceDict -> Exists2 CoerceDict -> Maybe (Exists2 CoerceDict)
    Exists2 (CoerceDict (f :: b -> c)) .* Exists2 (CoerceDict (g :: a -> b')) =
      case eqT :: Maybe (b :~: b') of
        Just Refl -> Just (Exists2 (CoerceDict (f . g)))
        Nothing -> Nothing

    -- Dynamically typed coercion composition over a list
    (..*) :: Exists2 CoerceDict -> [Exists2 CoerceDict] -> [Exists2 CoerceDict]
    f ..* gs = do
      g <- gs
      h <- maybe [] return (f .* g)
      return h

    fromIntegral' :: (Integral a, Integral b) => CoerceDict a b
    fromIntegral' = CoerceDict fromIntegral

    fromUnknown' :: CoerceDict Unknown a
    fromUnknown' = CoerceDict fromUnknown

    -- TODO: Implementing this (transitive closure of a set of coercions) will
    -- make things much nicer.

    -- coerciveClosure :: Typemap2 CoerceDict -> Typemap2 CoerceDict
    -- coerciveClosure basicCoercions = flip execState (mempty :: Typemap2 CoerceDict) $ do
    --   let basicCoercions' = Map.toList basicCoercions

    --       tryInsert continue (c :: CoerceDict a b) = do
    --         let entry = at (Proxy :: Proxy a, Proxy :: Proxy b)
    --         existing <- use entry
    --         case existing of
    --           Nothing -> entry .= Just (Exists2 c) >> continue
    --           _ -> return ()

    --   forM_ basicCoercions' $ \c1 -> forM_ basicCoercions' $ \c2 -> do
    --     undefined
