{-# LANGUAGE OverloadedStrings #-}

module Language.While.Syntax.Sugar where

import           Data.SBV                        (AlgReal)

import           Data.Vinyl.Curry

import           Language.Expression
import           Language.Expression.GeneralOp
import           Language.Expression.Util
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

(.=.) :: l -> WhileExpr l AlgReal -> Command l a
(.=.) = CAssign

(\\) :: Command l a -> Command l a -> Command l a
(\\) = CSeq

(^^^) :: WhileProp l Bool -> AnnCommand l () -> AnnCommand l ()
prop ^^^ command = CAnn (PropAnn prop ()) command

(.==) :: WhileExpr l AlgReal -> WhileExpr l AlgReal -> WhileExpr l Bool
(.==) = HWrap ... rcurry (Op OpEq)

(.<) :: WhileExpr l AlgReal -> WhileExpr l AlgReal -> WhileExpr l Bool
(.<) = HWrap ... rcurry (Op OpLT)

(.>) :: WhileExpr l AlgReal -> WhileExpr l AlgReal -> WhileExpr l Bool
(.>) = HWrap ... rcurry (Op OpGT)

(.<=) :: WhileExpr l AlgReal -> WhileExpr l AlgReal -> WhileExpr l Bool
(.<=) = HWrap ... rcurry (Op OpLE)

(.>=) :: WhileExpr l AlgReal -> WhileExpr l AlgReal -> WhileExpr l Bool
(.>=) = HWrap ... rcurry (Op OpGE)

(.&&) :: WhileExpr l Bool -> WhileExpr l Bool -> WhileExpr l Bool
(.&&) = HWrap ... rcurry (Op OpAnd)

(.||) :: WhileExpr l Bool -> WhileExpr l Bool -> WhileExpr l Bool
(.||) = HWrap ... rcurry (Op OpOr)

wenot :: WhileExpr l Bool -> WhileExpr l Bool
wenot = HWrap . rcurry (Op OpNot)
