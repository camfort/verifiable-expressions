{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Language.Verification.Expression.DSL
  (
  -- * Types
    Expr
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

import           Language.Verification.Expression           hiding (Expr)
import qualified Language.Verification.Expression           as E
import           Language.Verification.Expression.Operators
import           Language.Verification.SymClasses           as Classes


-- | Expressions
type Expr v a = E.Expr BasicOp v a

-- | Propositions over expressions
type Prop v a = E.Expr BoolOp (E.Expr BasicOp v) a

--------------------------------------------------------------------------------
--  Lifting
--------------------------------------------------------------------------------

-- | Embed a variable into an expression.
var :: v a -> E.Expr op v a
var = EVar

-- | Lift an expression into the land of propositions.
expr :: Expr v a -> Prop v a
expr = EVar

--------------------------------------------------------------------------------
--  Literal Operators
--------------------------------------------------------------------------------

-- | Embed a literal into an expression.
lit :: (SymValue a) => a -> Expr v a
lit = litOp

--------------------------------------------------------------------------------
--  Boolean Operators
--------------------------------------------------------------------------------

infixl 3 .&&
infixl 2 .||
infixr 1 .->
infix 1 .<->

enot :: SymBool b => Expr v b -> Expr v b
enot = boolOp . OpNot

(.&&) :: SymBool b => Expr v b -> Expr v b -> Expr v b
(.&&) = boolOp ... OpAnd

(.||) :: SymBool b => Expr v b -> Expr v b -> Expr v b
(.||) = boolOp ... OpOr

(.->) :: SymBool b => Expr v b -> Expr v b -> Expr v b
(.->) = boolOp ... OpImpl

(.<->) :: SymBool b => Expr v b -> Expr v b -> Expr v b
(.<->) = boolOp ... OpEquiv

--------------------------------------------------------------------------------
--  Numeric Operators
--------------------------------------------------------------------------------

infixl 6 .*
infixl 5 .+
infixl 5 .-

(.+) :: SymNum a => Expr v a -> Expr v a -> Expr v a
(.+) = numOp ... OpAdd

(.-) :: SymNum a => Expr v a -> Expr v a -> Expr v a
(.-) = numOp ... OpSub

(.*) :: SymNum a => Expr v a -> Expr v a -> Expr v a
(.*) = numOp ... OpMul

--------------------------------------------------------------------------------
--  Equality Operators
--------------------------------------------------------------------------------

infix 4 .==
infix 4 ./=

(.==) :: SymEq b a => Expr v a -> Expr v a -> Expr v b
(.==) = eqOp ... OpEq

(./=) :: SymEq b a => Expr v a -> Expr v a -> Expr v b
(./=) = enot ... (.==)

--------------------------------------------------------------------------------
--  Ordering Operators
--------------------------------------------------------------------------------

infix 4 .<
infix 4 .<=
infix 4 .>
infix 4 .>=

(.<) :: SymOrd b a => Expr v a -> Expr v a -> Expr v b
(.<) = ordOp ... OpLT

(.<=) :: SymOrd b a => Expr v a -> Expr v a -> Expr v b
(.<=) = ordOp ... OpLE

(.>) :: SymOrd b a => Expr v a -> Expr v a -> Expr v b
(.>) = ordOp ... OpGT

(.>=) :: SymOrd b a => Expr v a -> Expr v a -> Expr v b
(.>=) = ordOp ... OpGE

--------------------------------------------------------------------------------
--  Proposition Operators
--------------------------------------------------------------------------------

infixl 3 *&&
infixl 2 *||
infixr 1 *->
infix 1 *<->

plit :: SymBool b => b -> Prop v b
plit = expr . lit

pnot :: SymBool b => Prop v b -> Prop v b
pnot = EOp . OpNot

(*&&) :: SymBool b => Prop v b -> Prop v b -> Prop v b
(*&&) = EOp ... OpAnd

(*||) :: SymBool b => Prop v b -> Prop v b -> Prop v b
(*||) = EOp ... OpOr

(*->) :: SymBool b => Prop v b -> Prop v b -> Prop v b
(*->) x y = pnot x *|| y

(*<->) :: SymBool b => Prop v b -> Prop v b -> Prop v b
(*<->) x y = (x *-> y) *&& (y *-> x)

--------------------------------------------------------------------------------
--  Internal Combinators
--------------------------------------------------------------------------------

litOp x = EOp (Op0 (OpLit x))
boolOp  = EOp . Op1
numOp   = EOp . Op2
eqOp    = EOp . Op3
ordOp   = EOp . Op4

(...) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(f ... g) x y = f (g x y)
