{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}

{-|

Combinators for conveniently constructing expressions and propositions.

-}
module Language.Expression.DSL
  (
  -- * Types
    Expr
  , Expr'
  , PropOver
  , Prop
  -- * Lifting
  , var
  , expr
  -- * Propositions
  , plit
  , pnot
  , (*&&)
  , (*||)
  , (*->)
  , (*<->)
  -- * Literals
  , elit
  -- * Booleans
  , enot
  , (.&&)
  , (.||)
  -- * Numeric
  , (.+)
  , (.-)
  , (.*)
  -- * Equality
  , (.==)
  , (./=)
  -- * Ordering
  , (.<)
  , (.>)
  , (.<=)
  , (.>=)
  -- * Coercion
  , ecoerce
  -- * Classes
  , module Classes
  ) where

import           Control.Lens                  hiding ((...), (.>))

import           Language.Expression
import           Language.Expression.Classes   as Classes
import           Language.Expression.Operators

-- | Propositions over general expressions.
type PropOver = Expr LogicOp

-- | Propositions over expressions with the given list of operators.
type Prop ops v = Expr LogicOp (Expr' ops v)


-- type SimpleProp op expr a = 

--------------------------------------------------------------------------------
--  Lifting
--------------------------------------------------------------------------------

-- | Embed a variable into an expression.
var :: v a -> Expr' ops v a
var = Expr' . EVar

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

plit :: SymBool b => Bool -> PropOver expr b
plit = EOp . LogLit

pnot :: SymBool b => PropOver expr b -> PropOver expr b
pnot = EOp . LogNot

(*&&) :: SymBool b => PropOver expr b -> PropOver expr b -> PropOver expr b
(*&&) = EOp ... LogAnd

(*||) :: SymBool b => PropOver expr b -> PropOver expr b -> PropOver expr b
(*||) = EOp ... LogOr

(*->) :: SymBool b => PropOver expr b -> PropOver expr b -> PropOver expr b
(*->) = EOp ... LogImpl

(*<->) :: SymBool b => PropOver expr b -> PropOver expr b -> PropOver expr b
(*<->) = EOp ... LogEquiv

--------------------------------------------------------------------------------
--  Literal Operators
--------------------------------------------------------------------------------

-- | Embed a literal into an expression.
elit :: (ChooseOp LitOp ops, SymLit a) => a -> Expr' ops t a
elit = Expr' . EOp . review chooseOp . OpLit

--------------------------------------------------------------------------------
--  Boolean Operators
--------------------------------------------------------------------------------

infixl 3 .&&
infixl 2 .||

enot :: (SymBool a, ChooseOp BoolOp ops) => Expr' ops v a -> Expr' ops v a
enot = intoChoice . OpNot

(.&&) :: (SymBool a, ChooseOp BoolOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v a
(.&&) = intoChoice ... OpAnd

(.||) :: (SymBool a, ChooseOp BoolOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v a
(.||) = intoChoice ... OpOr

--------------------------------------------------------------------------------
--  Numeric Operators
--------------------------------------------------------------------------------

infixl 6 .*
infixl 5 .+
infixl 5 .-

(.+) :: (SymNum a, ChooseOp NumOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v a
(.+) = intoChoice ... OpAdd

(.-) :: (SymNum a, ChooseOp NumOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v a
(.-) = intoChoice ... OpSub

(.*) :: (SymNum a, ChooseOp NumOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v a
(.*) = intoChoice ... OpMul

--------------------------------------------------------------------------------
--  Equality Operators
--------------------------------------------------------------------------------

infix 4 .==
infix 4 ./=

(.==) :: (SymEq b a, ChooseOp EqOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v b
(.==) = intoChoice ... OpEq

(./=) :: (SymEq b a, ChooseOp EqOp ops, ChooseOp BoolOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v b
(./=) = enot ... (.==)

--------------------------------------------------------------------------------
--  Ordering Operators
--------------------------------------------------------------------------------

infix 4 .<
infix 4 .<=
infix 4 .>
infix 4 .>=

(.<) :: (SymOrd b a, ChooseOp OrdOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v b
(.<) = intoChoice ... OpLT

(.<=) :: (SymOrd b a, ChooseOp OrdOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v b
(.<=) = intoChoice ... OpLE

(.>) :: (SymOrd b a, ChooseOp OrdOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v b
(.>) = intoChoice ... OpGT

(.>=) :: (SymOrd b a, ChooseOp OrdOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v b
(.>=) = intoChoice ... OpGE

--------------------------------------------------------------------------------
--  Coercion Operators
--------------------------------------------------------------------------------

ecoerce :: (SymValue a, SymValue b, ChooseOp CoerceOp ops) => Expr' ops v a -> Expr' ops v b
ecoerce = intoChoice . OpCoerce

--------------------------------------------------------------------------------
--  Internal Combinators
--------------------------------------------------------------------------------

intoChoice :: (Operator op, ChooseOp op ops) => op (Expr' ops v) a -> Expr' ops v a
intoChoice  = Expr' . EOp . review chooseOp . hmapOp getExpr'

(...) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(f ... g) x y = f (g x y)
