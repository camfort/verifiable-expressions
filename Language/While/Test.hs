{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Language.While.Test where

import qualified Language.Expression           as V
import qualified Language.Expression.Operators as V
import           Language.Expression.Pretty
import           Language.Verification

import           Language.While.Hoare
import           Language.While.Hoare.Prover
import           Language.While.Prop
import           Language.While.Syntax
import           Language.While.Syntax.Sugar

import           Data.SBV                      (SMTConfig (..), defaultSMTCfg)

testCommandAnn :: Command String (PropAnn String ())
testCommandAnn =
  "Q" .=. 0   \\ (PEmbed ("R" `BEq` "x") `PAnd` PEmbed ("Q" `BEq` 0)) ^^^
  CWhile ("Y" .<= "R")
  ((PEmbed ("x" `BEq` ("R" + "Y" * "Q"))) ^^^
   (  "R" .=. "R" - "Y"
   \\ "Q" .=. "Q" + 1
   ))

testPrecond :: WhileProp String
testPrecond = PEmbed ("R" `BEq` "x")

testPostcond :: WhileProp String
testPostcond =
  PEmbed ("x" `BEq` ("R" + "Y" * "Q")) `PAnd`
  PEmbed ("R" .< "Y")

testConfig :: SMTConfig
testConfig = defaultSMTCfg { verbose = True }

testVcs :: Maybe [VProp String Bool]
testVcs = generateVCs testPrecond testPostcond testCommandAnn

test :: IO (Either (VerifierError String (V.Expr' V.StandardOps)) Bool)
test = runVerifierWith testConfig $ do
  query $ do
    checkPartialHoare testPrecond testPostcond testCommandAnn
