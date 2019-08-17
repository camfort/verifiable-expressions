{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

{-|

Propositions and combinators for conveniently constructing them.

-}
module Language.Expression.Prop
  (
    -- * Proposition Types
    Prop
  , Prop'
    -- * DSL
  , expr
  , plit
  , pnot
  , (*&&)
  , (*||)
  , (*->)
  , (*<->)
  , propAnd
  , propOr
    -- * HTraversable
  , LogicOp(..)
  ) where

import           Control.Applicative        (liftA2)
import           Data.List                  (foldl')
-- import           Data.Typeable

-- import           Data.Functor.Classes
import           Data.Functor.Identity

import           Data.SBV

import           Language.Expression
import           Language.Expression.Choice
import           Language.Expression.Pretty
import           Language.Expression.Util

-- | Propositions over general expressions.
type Prop = HFree LogicOp

-- | Propositions over expressions with the given list of operators.
type Prop' ops v = Prop (HFree' ops v)

--------------------------------------------------------------------------------
--  DSL
--------------------------------------------------------------------------------

infixl 3 *&&
infixl 2 *||
infixr 1 *->
infix 1 *<->

-- | Lift an expression into the land of propositions.
expr :: expr a -> Prop expr a
expr = HPure

plit :: Bool -> Prop expr Bool
plit = HWrap . LogLit

pnot :: Prop expr Bool -> Prop expr Bool
pnot = HWrap . LogNot

(*&&) :: Prop expr Bool -> Prop expr Bool -> Prop expr Bool
(*&&) = HWrap ... LogAnd

(*||) :: Prop expr Bool -> Prop expr Bool -> Prop expr Bool
(*||) = HWrap ... LogOr

(*->) :: Prop expr Bool -> Prop expr Bool -> Prop expr Bool
(*->) = HWrap ... LogImpl

(*<->) :: Prop expr Bool -> Prop expr Bool -> Prop expr Bool
(*<->) = HWrap ... LogEquiv

propAnd :: [Prop expr Bool] -> Prop expr Bool
propAnd []       = plit True
propAnd (x : xs) = foldl' (*&&) x xs

propOr :: [Prop expr Bool] -> Prop expr Bool
propOr []       = plit False
propOr (x : xs) = foldl' (*||) x xs


--------------------------------------------------------------------------------
--  The HTraversable
--------------------------------------------------------------------------------

-- | Logical operations
data LogicOp t a where
  LogLit :: Bool -> LogicOp t Bool
  LogNot :: t Bool -> LogicOp t Bool
  LogAnd :: t Bool -> t Bool -> LogicOp t Bool
  LogOr :: t Bool -> t Bool -> LogicOp t Bool
  LogImpl :: t Bool -> t Bool -> LogicOp t Bool
  LogEquiv :: t Bool -> t Bool -> LogicOp t Bool

instance HFunctor LogicOp
instance HTraversable LogicOp where
  htraverse f = \case
    LogLit b -> pure $ LogLit b
    LogNot x -> LogNot <$> f x
    LogAnd x y -> LogAnd <$> f x <*> f y
    LogOr x y -> LogOr <$> f x <*> f y
    LogImpl x y -> LogImpl <$> f x <*> f y
    LogEquiv x y -> LogEquiv <$> f x <*> f y

instance HFoldableAt Identity LogicOp where
  hfoldMap = implHfoldMap $ \case
    LogLit b -> pure b
    LogNot x -> not <$> x
    LogAnd x y -> liftA2 (&&) x y
    LogOr x y -> liftA2 (||) x y
    LogImpl x y -> liftA2 (||) (not <$> x) y
    LogEquiv x y -> liftA2 (&&) (liftA2 (||) (not <$> x) y) (liftA2 (||) (not <$> y) x)

instance HFoldableAt SBV LogicOp where
  hfoldMap = implHfoldMap $ \case
    LogLit b -> fromBool b
    LogNot x -> sNot x
    LogAnd x y -> x .&& y
    LogOr x y -> x .|| y
    LogImpl x y -> x .=> y
    LogEquiv x y -> x .<=> y

-- instance HEq LogicOp where
--   liftHEq _ _ (LogLit x) (LogLit y) = x == y
--   liftHEq le _ (LogNot x) (LogNot y) = le svEq x y
--   liftHEq le _ (LogAnd x1 x2) (LogAnd y1 y2) = le svEq x1 y1 && le svEq x2 y2
--   liftHEq le _ (LogOr x1 x2) (LogOr y1 y2) = le svEq x1 y1 && le svEq x2 y2
--   liftHEq le _ (LogImpl x1 x2) (LogImpl y1 y2) = le svEq x1 y1 && le svEq x2 y2
--   liftHEq le _ (LogEquiv x1 x2) (LogEquiv y1 y2) = le svEq x1 y1 && le svEq x2 y2
--   liftHEq _ _ _ _ = False

-- instance (Eq1 t) => Eq1 (LogicOp t) where liftEq = liftLiftEq

-- instance (Eq a, Eq1 t) => Eq (LogicOp t a) where (==) = eq1

instance Pretty2 LogicOp where
  prettys2Prec p = \case
    LogLit True -> \r -> "T" ++ r
    LogLit False -> \r -> "F" ++ r
    LogNot x -> showParen (p > 8) $ showString "¬ " . prettys1Prec 9 x
    LogAnd x y ->
      showParen (p > 3) $ prettys1Prec 4 x . showString " ∧ " . prettys1Prec 4 y
    LogOr  x y ->
      showParen (p > 2) $ prettys1Prec 3 x . showString " ∨ " . prettys1Prec 3 y
    LogImpl  x y ->
      showParen (p > 1) $ prettys1Prec 2 x . showString " -> " . prettys1Prec 2 y
    LogEquiv  x y ->
      showParen (p > 0) $ prettys1Prec 1 x . showString " <-> " . prettys1Prec 1 y

--------------------------------------------------------------------------------
--  Internal Combinators
--------------------------------------------------------------------------------

-- svEq :: (Typeable a, Typeable b, Eq a) => a -> b -> Bool
-- svEq (x :: a) (y :: b)
--   | Just Refl <- eqT :: Maybe (a :~: b) = x == y
--   | otherwise = False
