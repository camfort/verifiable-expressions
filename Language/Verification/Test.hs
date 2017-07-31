{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Language.Verification.Test where

import           Control.Lens
import           Data.Functor.Identity

import           Data.Map                                   (Map)
import qualified Data.Map                                   as Map
import           Data.SBV                                   hiding
                                                             (OrdSymbolic (..),
                                                             ( # ))

import           Language.Verification
import           Language.Verification.Expression
import           Language.Verification.Expression.DSL       hiding (Expr)
import           Language.Verification.Expression.Operators
import           Language.Verification.Expression.Pretty

--------------------------------------------------------------------------------
--  Test expression and propositions
--------------------------------------------------------------------------------

var' :: (SymWord a, Verifiable a) => l -> Expr op (Var l) a
var' = var . Var

testExpr1 :: Expr BasicOp (Var String) Integer
testExpr1 = var' "x" .* lit 5

testExpr2 :: Expr BasicOp (Var String) Integer
testExpr2 = var' "x" .* lit 10

testExpr3 :: Expr BasicOp (Var String) Bool
testExpr3 = testExpr1 .<= testExpr2

-- TODO: This is apparently not a theorem. Investigate!

testProp :: Prop (Var String) Bool
testProp = expr testExpr3

--------------------------------------------------------------------------------
--  Testing interaction with the verifier
--------------------------------------------------------------------------------

testVerifier :: Verifier String (Expr BasicOp) Bool
testVerifier = query $ checkProp testProp

testConfig :: SMTConfig
testConfig = defaultSMTCfg { verbose = True }

test :: IO (Either (VerifierError String (Expr BasicOp)) Bool)
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

testProp' :: PropOn (Expr BasicOp Maybe) Bool
testProp' = hmapOp (hmapOp testGetVar) testProp

testEval :: Maybe Bool
testEval = evalOp (hmapOp evalOp testProp')
