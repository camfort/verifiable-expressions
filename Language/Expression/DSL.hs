{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}

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
  -- * Literals
  , lit
  -- * Booleans
  , enot
  , (.&&)
  , (.||)
  , (.->)
  , (.<->)
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
  -- * Propositions
  , plit
  , pnot
  , (*&&)
  , (*||)
  , (*->)
  , (*<->)
  -- * Classes
  , module Classes
  ) where

import           Control.Lens                  hiding ((...), (.>))

import           Language.Expression
import           Language.Expression.Classes   as Classes
import           Language.Expression.Operators

-- | Propositions over general expressions.
type PropOver expr a = Expr' '[BoolOp] expr a

-- | Propositions over expressions with the given list of operators.
type Prop ops v a = Expr' '[BoolOp] (Expr' ops v) a

--------------------------------------------------------------------------------
--  Lifting
--------------------------------------------------------------------------------

-- | Embed a variable into an expression.
var :: v a -> Expr' ops v a
var = Expr' . EVar

-- | Lift an expression into the land of propositions.
expr :: expr a -> PropOver expr a
expr = Expr' . EVar

--------------------------------------------------------------------------------
--  Literal Operators
--------------------------------------------------------------------------------

-- | Embed a literal into an expression.
lit :: (ChooseOp LitOp ops, SymLit a) => a -> Expr' ops t a
lit = Expr' . EOp . review chooseOp . OpLit

--------------------------------------------------------------------------------
--  Boolean Operators
--------------------------------------------------------------------------------

infixl 3 .&&
infixl 2 .||
infixr 1 .->
infix 1 .<->

enot :: (SymBool a, ChooseOp BoolOp ops) => Expr' ops v a -> Expr' ops v a
enot = liftOp . OpNot

(.&&) :: (SymBool a, ChooseOp BoolOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v a
(.&&) = liftOp ... OpAnd

(.||) :: (SymBool a, ChooseOp BoolOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v a
(.||) = liftOp ... OpOr

(.->) :: (SymBool a, ChooseOp BoolOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v a
(.->) = liftOp ... OpImpl

(.<->) :: (SymBool a, ChooseOp BoolOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v a
(.<->) = liftOp ... OpEquiv

--------------------------------------------------------------------------------
--  Numeric Operators
--------------------------------------------------------------------------------

infixl 6 .*
infixl 5 .+
infixl 5 .-

(.+) :: (SymNum a, ChooseOp NumOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v a
(.+) = liftOp ... OpAdd

(.-) :: (SymNum a, ChooseOp NumOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v a
(.-) = liftOp ... OpSub

(.*) :: (SymNum a, ChooseOp NumOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v a
(.*) = liftOp ... OpMul

--------------------------------------------------------------------------------
--  Equality Operators
--------------------------------------------------------------------------------

infix 4 .==
infix 4 ./=

(.==) :: (SymEq b a, ChooseOp EqOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v b
(.==) = liftOp ... OpEq

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
(.<) = liftOp ... OpLT

(.<=) :: (SymOrd b a, ChooseOp OrdOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v b
(.<=) = liftOp ... OpLE

(.>) :: (SymOrd b a, ChooseOp OrdOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v b
(.>) = liftOp ... OpGT

(.>=) :: (SymOrd b a, ChooseOp OrdOp ops) => Expr' ops v a -> Expr' ops v a -> Expr' ops v b
(.>=) = liftOp ... OpGE

--------------------------------------------------------------------------------
--  Proposition Operators
--------------------------------------------------------------------------------

infixl 3 *&&
infixl 2 *||
infixr 1 *->
infix 1 *<->

plit :: (SymLit a, ChooseOp LitOp ops) => a -> PropOver (Expr' ops t) a
plit = expr . lit

pnot :: SymBool b => PropOver expr b -> PropOver expr b
pnot = enot

(*&&) :: SymBool b => PropOver expr b -> PropOver expr b -> PropOver expr b
(*&&) = (.&&)

(*||) :: SymBool b => PropOver expr b -> PropOver expr b -> PropOver expr b
(*||) = (.||)

(*->) :: SymBool b => PropOver expr b -> PropOver expr b -> PropOver expr b
(*->) = (.->)

(*<->) :: SymBool b => PropOver expr b -> PropOver expr b -> PropOver expr b
(*<->) = (.<->)

--------------------------------------------------------------------------------
--  Internal Combinators
--------------------------------------------------------------------------------

liftOp :: (Operator op, ChooseOp op ops) => op (Expr' ops v) a -> Expr' ops v a
liftOp  = Expr' . EOp . review chooseOp . hmapOp getExpr'

(...) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(f ... g) x y = f (g x y)
