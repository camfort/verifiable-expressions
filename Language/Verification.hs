{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeOperators             #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

module Language.Verification
  (
  -- * The verification monad
    Verifier
  , runVerifier
  , VerifierError(..)

  -- * Verifiable types and variables
  , VerifierSymbol
  , Verifiable
  , Var(..)

  -- * Verifier actions
  , checkProp

  -- * Miscellaneous combinators
  , subVar
  ) where

import           Data.Data

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.State

import           Data.Map                                   (Map)
import qualified Data.Map                                   as Map
import           Data.SBV                                   hiding (( # ))

import           Language.Verification.Expression
import           Language.Verification.Expression.Operators


--------------------------------------------------------------------------------
--  Internal Types
--------------------------------------------------------------------------------

data VerifierSymbol f
  = VSInteger (f Integer)
  | VSBool (f Bool)
  | VSReal (f AlgReal)

makePrisms ''VerifierSymbol

class Typeable a => Verifiable a where
  _Symbol :: Prism' (VerifierSymbol f) (f a)

instance Verifiable Integer where
  _Symbol = _VSInteger

instance Verifiable Bool where
  _Symbol = _VSBool

instance Verifiable AlgReal where
  _Symbol = _VSReal

data Var a where
  Var :: (SymWord a, Verifiable a) => String -> Var a

data VerifierState (expr :: (* -> *) -> * -> *) =
  VerifierState
  { _varSymbols    :: Map String (VerifierSymbol SBV)
  }

makeLenses ''VerifierState

vs0 :: VerifierState expr
vs0 = VerifierState mempty

--------------------------------------------------------------------------------
--  Exposed Types
--------------------------------------------------------------------------------

data VerifierError (expr :: (* -> *) -> * -> *)
  = VEMismatchedSymbolType String
  -- ^ The same variable was used for two different symbol types
  deriving (Show, Eq, Ord, Data, Typeable)

data Verifier expr a =
  Verifier
  { getVerifier :: StateT (VerifierState expr) (ExceptT (VerifierError expr) Symbolic) a
  }
  deriving (Functor)

runVerifier :: Verifier expr a -> IO (Either (VerifierError expr) a)
runVerifier (Verifier action) = runSMT (runExceptT (evalStateT action vs0))

instance Applicative (Verifier expr) where
  pure = return
  (<*>) = ap

instance Monad (Verifier expr) where
  return = Verifier . return

  Verifier x >>= f = Verifier (x >>= getVerifier . f)

instance MonadIO (Verifier expr) where
  liftIO = Verifier . liftIO

--------------------------------------------------------------------------------
--  Exposed Functions
--------------------------------------------------------------------------------

-- | If the two variables match in both type and name, return the given
-- expression. Otherwise, return an expression just containing this variable.
--
-- This is substitution into an expression, where the old expression is just a
-- variable.
subVar :: forall expr a b. (Substitutive expr) => expr Var a -> Var a -> Var b -> expr Var b
subVar newExpr (Var targetName) thisVar@(Var thisName) =
  case eqT :: Maybe (a :~: b) of
    Just Refl | thisName == targetName -> newExpr
    _ -> pureVar thisVar

checkProp :: (Substitutive expr, HoistOp SBV expr) => PropOn (expr Var) Bool -> Verifier expr Bool
checkProp prop = do
  symbolicProp <- propToSBV prop
  liftIO (isTheorem symbolicProp)

--------------------------------------------------------------------------------
--  Internal Functions
--------------------------------------------------------------------------------

propToSBV :: (Substitutive expr, HoistOp SBV expr) => PropOn (expr Var) Bool -> Verifier expr SBool
propToSBV prop = do
  propWithSymbols <- traverseOp (traverseOp symbolVar) prop

  let evalExpr' = runIdentity . evalOp . hoistOp pure
      result = evalExpr' (mapOp evalExpr' propWithSymbols)

  return result

liftSymbolic :: Symbolic a -> Verifier v a
liftSymbolic = Verifier . lift . lift

symbolVar :: Var a -> Verifier expr (SBV a)
symbolVar (Var varName) = do
  storedSymbol <- Verifier $ use (varSymbols . at varName)

  case storedSymbol of
    Just s -> maybe (Verifier $ throwError (VEMismatchedSymbolType varName))
              return
              (s ^? _Symbol)
    Nothing -> do
      newSymbol <- liftSymbolic (symbolic varName)
      Verifier $ varSymbols . at varName .= Just (_Symbol # newSymbol)
      return newSymbol

--------------------------------------------------------------------------------
--  Tests
--------------------------------------------------------------------------------

testExpr1 :: Expr BasicOp Var Integer
testExpr1 = EOp (EVar (Var "x") `bMul` EOp (bLit 10))

testExpr2 :: Expr BasicOp Var Integer
testExpr2 = EOp (EVar (Var "x") `bMul` EOp (bLit 5))

testExpr3 :: Expr BasicOp Var Bool
testExpr3 = EOp (testExpr1 `bGT` testExpr2)

testProp :: PropOn (Expr BasicOp Var) Bool
testProp = EVar testExpr3

testVarmap :: Map String (VerifierSymbol Identity)
testVarmap = Map.fromList
  [ ("x", VSInteger 5)
  ]

testGetVar :: Var a -> Maybe a
testGetVar (Var v) = testVarmap ^? at v . _Just . _Symbol . _Wrapped

testProp' :: PropOn (Expr BasicOp Maybe) Bool
testProp' = mapOp (mapOp testGetVar) testProp

testEval :: Maybe Bool
testEval = evalOp (mapOp evalOp testProp')

testVerifier :: Verifier (Expr BasicOp) Bool
testVerifier = checkProp testProp

test :: IO (Either (VerifierError (Expr BasicOp)) Bool)
test = runVerifier testVerifier
