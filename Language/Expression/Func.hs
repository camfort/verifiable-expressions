{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TypeInType                 #-}

module Language.Expression.Func where

import           Control.Applicative   (liftA2)
import           Data.Kind (Constraint, Type)
import           Data.Monoid           (All (..), Any (..))
import           Data.Typeable         (Proxy (..))

import           Data.Functor.Identity

import           Data.Vinyl
import           Data.Vinyl.TypeLevel

--------------------------------------------------------------------------------
--  Type-level stuff
--------------------------------------------------------------------------------

data a :& b

data Uncurry f p where
  Uncurry :: { getUncurry :: f a b } -> Uncurry f (a :& b)

data C (c :: k -> Constraint) (a :: k) where
  C :: c a => C c a

--------------------------------------------------------------------------------
--  Finite types
--------------------------------------------------------------------------------

class (Enum a, Bounded a) => Finite a
instance (Enum a, Bounded a) => Finite a

--------------------------------------------------------------------------------
--  Functions over lists of arguments
--------------------------------------------------------------------------------

newtype Func' f args result = Func { appF :: Rec f args -> result }
  deriving (Functor, Applicative, Monoid)

type Func = Func' Identity

type FNil = Func '[]

appF1 :: Func' f (a ': args) result -> f a -> Func' f args result
appF1 f x = Func $ \args -> appF f (x :& args)

foldMapF1
  :: (Finite a, Monoid m)
  => (result -> m) -> Func (a ': args) result -> Func args m
foldMapF1 f g =
  let g' = fmap f g
  in foldMap (appF1 g') [minBound .. maxBound]

andF1
  :: (Enum a, Bounded a)
  => Func (a : args) Bool -> Func args Bool
andF1 = fmap getAll . foldMapF1 All

orF1
  :: (Enum a, Bounded a)
  => Func (a : args) Bool -> Func args Bool
orF1 = fmap getAny . foldMapF1 Any

data CFunc c f args result where
  CFunc :: { constraintsC :: Rec (C c) args
            , appC :: Rec f args -> result }
         -> CFunc c f args result

deriving instance Functor (CFunc c f args)

instance (RecApplicative (args :: [Type]), AllConstrained c args) =>
         Applicative (CFunc c f args) where
  pure = CFunc (rpureConstrained (Proxy :: Proxy c) C) . pure
  (<*>) = apC

apC :: CFunc c0 f args (a -> b) -> CFunc c f args a -> CFunc c f args b
apC (CFunc _ f1) (CFunc cs f2) = CFunc cs (f1 <*> f2)

liftC2 :: (a -> b -> r)
       -> CFunc c0 f args a
       -> CFunc c f args b
       -> CFunc c f args r
liftC2 f x y = (f <$> x) `apC` y

appC1 :: CFunc c f (a ': args) result -> (c a => f a) -> CFunc c f args result
appC1 (CFunc (C :& cs) f) x = CFunc cs (\args -> f (x :& args))
