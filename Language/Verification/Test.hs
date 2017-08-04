{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Language.Verification.Test where

import           Control.Lens                  hiding ((.>))
import           Data.Functor.Identity

import           Data.Map                      (Map)
import qualified Data.Map                      as Map

import           Language.Expression.Pretty
import           Language.Verification hiding (Expr)

--------------------------------------------------------------------------------
--  Test expression and propositions
--------------------------------------------------------------------------------

var' :: (Verifiable a, SymWord a) => l -> Expr' ops (Var l) a
var' = var . Var

-- TODO: This is apparently not a theorem. Investigate!

testProp :: Prop StandardOps (Var String) Bool
testProp =
  expr (var' "x" .>= elit (0 :: Integer)) *->
  expr (var' "x" .* elit (5 :: Integer) .<= var' "x" .* elit 10)

--------------------------------------------------------------------------------
--  Testing interaction with the verifier
--------------------------------------------------------------------------------

testVerifier :: Verifier String (Expr' StandardOps) Bool
testVerifier = query $ checkProp testProp

testConfig :: SMTConfig
testConfig = defaultSMTCfg { verbose = True }

test :: IO (Either (VerifierError String (Expr' StandardOps)) Bool)
test = runVerifierWith testConfig testVerifier

--------------------------------------------------------------------------------
--  Testing pure evaluation
--------------------------------------------------------------------------------

testVarmap :: Map String (VerifierSymbol Identity)
testVarmap = Map.fromList
  [ ("x", _Symbol # (5 :: Identity Integer))
  ]

testGetVar :: (Var String) a -> Maybe a
testGetVar (Var v) = testVarmap ^? at v . _Just . _Symbol . _Wrapped

testProp' :: PropOver (Expr' StandardOps Maybe) Bool
testProp' = hmapOp (hmapOp testGetVar) testProp

testEval :: Maybe Bool
testEval = getPureEval $ evalOp' (evalOp' PureEval) testProp'
