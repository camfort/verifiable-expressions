{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Language.While.Test where

import           Language.Expression.Pretty
import           Language.Expression.Prop
import           Language.Verification

import           Language.While.Hoare
import           Language.While.Hoare.Prover
import           Language.While.Syntax
import           Language.While.Syntax.Sugar

import           Data.SBV                    (SMTConfig (..), defaultSMTCfg)

testCommandAnn :: Command String (PropAnn String ())
testCommandAnn =
  "Q" .=. 0   \\ (expr ("R" .== "x") *&& expr ("Q" .== 0)) ^^^
  CWhile ("Y" .<= "R")
  ((expr ("x" .== ("R" + "Y" * "Q"))) ^^^
   (  "R" .=. "R" - "Y"
   \\ "Q" .=. "Q" + 1
   ))

testPrecond :: WhileProp String Bool
testPrecond = expr ("R" .== "x")

testPostcond :: WhileProp String Bool
testPostcond =
  expr ("x" .== ("R" + "Y" * "Q")) *&&
  expr ("R" .< "Y")

testConfig :: SMTConfig
testConfig = defaultSMTCfg { verbose = False }

testVcs :: Maybe [VProp String Bool]
testVcs = generateVCs testPrecond testPostcond testCommandAnn

test :: IO (Either (VerifierError (WhileVar String)) Bool)
test = runVerifierWith testConfig $ query $
  checkPartialHoare testPrecond testPostcond testCommandAnn
