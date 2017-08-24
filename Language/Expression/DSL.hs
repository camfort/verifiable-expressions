{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}

{-|

Combinators for conveniently constructing expressions and propositions.

-}
module Language.Expression.DSL
  (
  -- * Lifting
    expr
  -- * Propositions
  , PropOver
  , Prop
  , plit
  , pnot
  , (*&&)
  , (*||)
  , (*->)
  , (*<->)
  , propAnd
  , propOr
  -- * Operators
  , module Operators
  -- * Classes
  , module Classes
  ) where

import           Data.List (foldl')

import           Language.Expression
import           Language.Expression.Ops.Classes   as Classes
import           Language.Expression.Ops.Standard as Operators

-- | Propositions over general expressions.
type PropOver = Expr LogicOp

-- | Propositions over expressions with the given list of operators.
type Prop ops v = PropOver (Expr' ops v)

--------------------------------------------------------------------------------
--  Lifting
--------------------------------------------------------------------------------

-- | Lift an expression into the land of propositions.
expr :: expr a -> PropOver expr a
expr = EVar

--------------------------------------------------------------------------------
--  Proposition Operators
--------------------------------------------------------------------------------

infixl 3 *&&
infixl 2 *||
infixr 1 *->
infix 1 *<->

plit :: Bool -> PropOver expr Bool
plit = EOp . LogLit

pnot :: PropOver expr Bool -> PropOver expr Bool
pnot = EOp . LogNot

(*&&) :: PropOver expr Bool -> PropOver expr Bool -> PropOver expr Bool
(*&&) = EOp ... LogAnd

(*||) :: PropOver expr Bool -> PropOver expr Bool -> PropOver expr Bool
(*||) = EOp ... LogOr

(*->) :: PropOver expr Bool -> PropOver expr Bool -> PropOver expr Bool
(*->) = EOp ... LogImpl

(*<->) :: PropOver expr Bool -> PropOver expr Bool -> PropOver expr Bool
(*<->) = EOp ... LogEquiv

propAnd :: [PropOver expr Bool] -> PropOver expr Bool
propAnd [] = plit True
propAnd (x : xs) = foldl' (*&&) x xs

propOr :: [PropOver expr Bool] -> PropOver expr Bool
propOr [] = plit False
propOr (x : xs) = foldl' (*||) x xs

--------------------------------------------------------------------------------
--  Internal Combinators
--------------------------------------------------------------------------------

-- intoChoice :: (Operator op, ChooseOp op ops) => op (Expr' ops v) a -> Expr' ops v a
-- intoChoice  = Expr' . EOp . review chooseOp . hmapOp getExpr'

(...) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(f ... g) x y = f (g x y)
