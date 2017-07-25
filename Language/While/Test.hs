{-# LANGUAGE OverloadedStrings #-}

module Language.While.Test where

import           Language.While.Hoare
import           Language.While.Hoare.Prover
import           Language.While.Pretty
import           Language.While.Syntax
import           Language.While.Syntax.Sugar
import           Language.While.Prop


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
  "Q" .=. 0   \\ (PEmbed ("R" `BEq` "X") `PAnd` PEmbed ("Q" `BEq` 0)) ^^^
  CWhile ("Y" .<= "R")
  ((PEmbed ("X" `BEq` ("R" + "Y" * "Q"))) ^^^
   (  "R" .=. "R" - "Y"
   \\ "Q" .=. "Q" + 1
   ))

testPrecond :: WhileProp l
testPrecond = PLit True

testPostcond :: WhileProp String
testPostcond =
  PEmbed ("X" `BEq` ("R" + "Y" * "Q")) `PAnd`
  PEmbed ("R" .< "Y")

testVcs :: Maybe [WhileProp String]
testVcs = generateVcs testPrecond testPostcond testCommandAnn

test :: IO Bool
test = provePartialHoare testPrecond testPostcond testCommandAnn
