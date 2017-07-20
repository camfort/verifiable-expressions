{-# LANGUAGE OverloadedStrings #-}

module Language.While.Test where

import           Language.While.Syntax
import           Language.While.Syntax.Sugar
import           Language.While.Hoare
import           Language.While.Hoare.Prover


testCommand =
  "R" .=. "X" \\
  "Q" .=. 0   \\
  CWhile ("Y" .<= "R")
  (  "R" .=. "R" - "Y"
  \\ "Q" .=. "Q" + 1
  )

testCommandAnn =
  "R" .=. "X" \\
  "Q" .=. 0   \\ (PBexpr ("R" `BEq` "X") `PAnd` PBexpr ("Q" `BEq` 0)) ^^^
  CWhile ("Y" .<= "R")
  ((PBexpr ("X" `BEq` ("R" + "Y" * "Q"))) ^^^
   (  "R" .=. "R" - "Y"
   \\ "Q" .=. "Q" + 1
   ))

testPrecond = PTrue

testPostcond =
  PBexpr ("X" `BEq` ("R" + "Y" * "Q")) `PAnd`
  PBexpr ("R" .< "Y")

-- provePartialHoare :: Prop String -> Prop String -> AnnCommand String a -> IO (Maybe Bool)

test = provePartialHoare testPrecond testPostcond testCommandAnn
