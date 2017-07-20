{-# LANGUAGE OverloadedStrings #-}

module Language.While.Test where

import           Language.While.Hoare
import           Language.While.Hoare.Prover
import           Language.While.Pretty
import           Language.While.Syntax
import           Language.While.Syntax.Sugar


testCommand :: Command [Char] a
testCommand =
  "R" .=. "X" \\
  "Q" .=. 0   \\
  CWhile ("Y" .<= "R")
  (  "R" .=. "R" - "Y"
  \\ "Q" .=. "Q" + 1
  )

testCommandAnn :: Command String (PropAnn String ())
testCommandAnn =
  "R" .=. "X" \\
  "Q" .=. 0   \\ (PBexpr ("R" `BEq` "X") `PAnd` PBexpr ("Q" `BEq` 0)) ^^^
  CWhile ("Y" .<= "R")
  ((PBexpr ("X" `BEq` ("R" + "Y" * "Q"))) ^^^
   (  "R" .=. "R" - "Y"
   \\ "Q" .=. "Q" + 1
   ))

testPrecond :: Prop l
testPrecond = PTrue

testPostcond :: Prop String
testPostcond =
  PBexpr ("X" `BEq` ("R" + "Y" * "Q")) `PAnd`
  PBexpr ("R" .< "Y")

testVcs :: Maybe [Prop String]
testVcs = generateVcs testPrecond testPostcond testCommandAnn

test :: IO (Maybe Bool)
test = provePartialHoare testPrecond testPostcond testCommandAnn
