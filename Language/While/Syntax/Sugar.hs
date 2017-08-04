{-# LANGUAGE OverloadedStrings #-}

module Language.While.Syntax.Sugar where

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

(.<) :: WhileExpr l Integer -> WhileExpr l Integer -> WhileExpr l Bool
(.<) = BLess

(.<=) :: WhileExpr l Integer -> WhileExpr l Integer -> WhileExpr l Bool
(.<=) = BLessEq

(.>) :: WhileExpr l Integer -> WhileExpr l Integer -> WhileExpr l Bool
(.>) = flip BLess

(.>=) :: WhileExpr l Integer -> WhileExpr l Integer -> WhileExpr l Bool
(.>=) = flip BLessEq

(.&&) :: WhileExpr l Bool -> WhileExpr l Bool -> WhileExpr l Bool
(.&&) = BAnd

(.||) :: WhileExpr l Bool -> WhileExpr l Bool -> WhileExpr l Bool
(.||) = BOr

