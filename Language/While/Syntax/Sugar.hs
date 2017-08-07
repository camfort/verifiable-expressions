{-# LANGUAGE OverloadedStrings #-}

module Language.While.Syntax.Sugar where

import           Language.Expression
import           Language.Expression.Curry
import           Language.Expression.Ops.General
import           Language.While.Hoare
import           Language.While.Syntax

infix 1 .=.
infixr 0 \\
infix 3 ^^^
infix 8 .<
infix 8 .<=
infix 8 .>
infix 8 .>=
infixr 7 .&&
infixr 6 .||

(.=.) :: l -> WhileExpr l Integer -> Command l a
(.=.) = CAssign

(\\) :: Command l a -> Command l a -> Command l a
(\\) = CSeq

(^^^) :: WhileProp l Bool -> AnnCommand l () -> AnnCommand l ()
prop ^^^ command = CAnn (PropAnn prop ()) command

(.==) :: WhileExpr l Integer -> WhileExpr l Integer -> WhileExpr l Bool
(.==) = EOp ... rcurry (Op OpEq)

(.<) :: WhileExpr l Integer -> WhileExpr l Integer -> WhileExpr l Bool
(.<) = EOp ... rcurry (Op OpLT)

(.>) :: WhileExpr l Integer -> WhileExpr l Integer -> WhileExpr l Bool
(.>) = EOp ... rcurry (Op OpGT)

(.<=) :: WhileExpr l Integer -> WhileExpr l Integer -> WhileExpr l Bool
(.<=) = EOp ... rcurry (Op OpLE)

(.>=) :: WhileExpr l Integer -> WhileExpr l Integer -> WhileExpr l Bool
(.>=) = EOp ... rcurry (Op OpGE)

(.&&) :: WhileExpr l Bool -> WhileExpr l Bool -> WhileExpr l Bool
(.&&) = EOp ... rcurry (Op OpAnd)

(.||) :: WhileExpr l Bool -> WhileExpr l Bool -> WhileExpr l Bool
(.||) = EOp ... rcurry (Op OpOr)

wenot :: WhileExpr l Bool -> WhileExpr l Bool
wenot = EOp . rcurry (Op OpNot)
