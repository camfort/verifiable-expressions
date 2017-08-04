{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Language.While.Test where

import           Language.Expression.Pretty
import           Language.Verification       hiding ((.<), (.<=))

import           Language.While.Hoare
import           Language.While.Hoare.Prover
import           Language.While.Prop
import           Language.While.Syntax
import           Language.While.Syntax.Sugar

import           Data.SBV                    (SMTConfig (..), defaultSMTCfg)

testCommandAnn :: Command String (PropAnn String ())
testCommandAnn =
  "Q" .=. 0   \\ (SVar ("R" `BEq` "x") `PAnd` SVar ("Q" `BEq` 0)) ^^^
  CWhile ("Y" .<= "R")
  ((SVar ("x" `BEq` ("R" + "Y" * "Q"))) ^^^
   (  "R" .=. "R" - "Y"
   \\ "Q" .=. "Q" + 1
   ))

testPrecond :: WhileProp String
testPrecond = SVar ("R" `BEq` "x")

testPostcond :: WhileProp String
testPostcond =
  SVar ("x" `BEq` ("R" + "Y" * "Q")) `PAnd`
  SVar ("R" .< "Y")

testConfig :: SMTConfig
testConfig = defaultSMTCfg { verbose = True }

testVcs :: Maybe [VProp String Bool]
testVcs = generateVCs testPrecond testPostcond testCommandAnn

test :: IO (Either (VerifierError String (Expr' StandardOps)) Bool)
test = runVerifierWith testConfig $ do
  query $ do
    checkPartialHoare testPrecond testPostcond testCommandAnn
