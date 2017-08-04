{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Language.While.Test where

import           Language.Expression.Pretty
import           Language.Verification
import           Language.Expression.DSL ((*&&), expr)

import           Language.While.Hoare
import           Language.While.Hoare.Prover
import           Language.While.Syntax
import           Language.While.Syntax.Sugar

import           Data.SBV                    (SMTConfig (..), defaultSMTCfg)

testCommandAnn :: Command String (PropAnn String ())
testCommandAnn =
  "Q" .=. 0   \\ (expr ("R" `BEq` "x") *&& expr ("Q" `BEq` 0)) ^^^
  CWhile ("Y" .<= "R")
  ((expr ("x" `BEq` ("R" + "Y" * "Q"))) ^^^
   (  "R" .=. "R" - "Y"
   \\ "Q" .=. "Q" + 1
   ))

testPrecond :: WhileProp String Bool
testPrecond = expr ("R" `BEq` "x")

testPostcond :: WhileProp String Bool
testPostcond =
  expr ("x" `BEq` ("R" + "Y" * "Q")) *&&
  expr ("R" .< "Y")

testConfig :: SMTConfig
testConfig = defaultSMTCfg { verbose = True }

testVcs :: Maybe [VProp String Bool]
testVcs = generateVCs testPrecond testPostcond testCommandAnn

test :: IO (Either (VerifierError String (Expr WhileOp)) Bool)
test = runVerifierWith testConfig $ do
  query $ do
    checkPartialHoare testPrecond testPostcond testCommandAnn
