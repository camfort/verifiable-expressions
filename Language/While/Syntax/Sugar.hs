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

(.=.) :: l -> Expr l -> Command l a
(.=.) = CAssign

(\\) :: Command l a -> Command l a -> Command l a
(\\) = CSeq

(^^^) :: WhileProp l -> AnnCommand l () -> AnnCommand l ()
prop ^^^ command = CAnn (PropAnn prop ()) command

(.<) :: Expr l -> Expr l -> Bexpr l
(.<) = BLess

(.<=) :: Expr l -> Expr l -> Bexpr l
(.<=) = BLessEq

(.>) :: Expr l -> Expr l -> Bexpr l
(.>) = flip BLess

(.>=) :: Expr l -> Expr l -> Bexpr l
(.>=) = flip BLessEq

(.&&) :: Bexpr l -> Bexpr l -> Bexpr l
(.&&) = BAnd

(.||) :: Bexpr l -> Bexpr l -> Bexpr l
(.||) = BOr

