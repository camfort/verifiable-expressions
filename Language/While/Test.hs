{-# LANGUAGE OverloadedStrings #-}

module Language.While.Test where

import           Language.Verification.Expression.Pretty
import           Language.Verification                      (VerifierError, runVerifierWith)
import qualified Language.Verification.Expression           as V
import qualified Language.Verification.Expression.Operators as V

import           Language.While.Hoare
import           Language.While.Hoare.Prover
import           Language.While.Prop
import           Language.While.Syntax
import           Language.While.Syntax.Sugar

import Data.SBV (SMTConfig(..), defaultSMTCfg)

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

testConfig :: SMTConfig
testConfig = defaultSMTCfg { verbose = True }

testVcs :: Maybe [VProp String Bool]
testVcs = generateVCs testPrecond testPostcond testCommandAnn

test :: IO (Either (VerifierError String (V.Expr V.BasicOp)) Bool)
test = runVerifierWith testConfig $ do
  provePartialHoare testPrecond testPostcond testCommandAnn
