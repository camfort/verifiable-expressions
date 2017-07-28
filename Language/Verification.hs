{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
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
--  Verifiable
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

--------------------------------------------------------------------------------
--  Internal Types
--------------------------------------------------------------------------------

data VerifierState l (expr :: (* -> *) -> * -> *) =
  VerifierState
  { _varSymbols    :: Map l (VerifierSymbol SBV)
  }

makeLenses ''VerifierState

vs0 :: Location l => VerifierState l expr
vs0 = VerifierState mempty

--------------------------------------------------------------------------------
--  Exposed Types
--------------------------------------------------------------------------------

class (Ord l) => Location l where
  locationName :: l -> String

instance Location String where locationName = id

-- | A variable with locations in @l@ representing values of type @a@.
data Var l a where
  Var :: (SymWord a, Verifiable a) => l -> Var l a

data VerifierError l (expr :: (* -> *) -> * -> *)
  = VEMismatchedSymbolType l
  -- ^ The same variable was used for two different symbol types
  deriving (Show, Eq, Ord, Data, Typeable)

data Verifier l expr a =
  Verifier
  { getVerifier :: StateT (VerifierState l expr) (ExceptT (VerifierError l expr) Symbolic) a
  }
  deriving (Functor)

runVerifier :: Location l => Verifier l expr a -> IO (Either (VerifierError l expr) a)
runVerifier (Verifier action) = runSMT (runExceptT (evalStateT action vs0))

instance Applicative (Verifier l expr) where
  pure = return
  (<*>) = ap

instance Monad (Verifier l expr) where
  return = Verifier . return

  Verifier x >>= f = Verifier (x >>= getVerifier . f)

instance MonadIO (Verifier l expr) where
  liftIO = Verifier . liftIO

--------------------------------------------------------------------------------
--  Exposed Functions
--------------------------------------------------------------------------------

-- | If the two variables match in both type and name, return the given
-- expression. Otherwise, return an expression just containing this variable.
--
-- This is substitution into an expression, where the old expression is just a
-- variable.
subVar :: forall expr a b l. (Substitutive expr, Eq l) => expr (Var l) a -> Var l a -> Var l b -> expr (Var l) b
subVar newExpr (Var targetName) thisVar@(Var thisName) =
  case eqT :: Maybe (a :~: b) of
    Just Refl | thisName == targetName -> newExpr
    _ -> pureVar thisVar

checkProp :: (Substitutive expr, HoistOp SBV expr, Location l) => PropOn (expr (Var l)) Bool -> Verifier l expr Bool
checkProp prop = do
  symbolicProp <- propToSBV prop
  liftIO (isTheorem symbolicProp)

--------------------------------------------------------------------------------
--  Internal Functions
--------------------------------------------------------------------------------

propToSBV :: (Substitutive expr, HoistOp SBV expr, Location l) => PropOn (expr (Var l)) Bool -> Verifier l expr SBool
propToSBV prop = do
  propWithSymbols <- traverseOp (traverseOp symbolVar) prop

  let evalExpr' = runIdentity . evalOp . hoistOp pure
      result = evalExpr' (mapOp evalExpr' propWithSymbols)

  return result

liftSymbolic :: Symbolic a -> Verifier l v a
liftSymbolic = Verifier . lift . lift

symbolVar :: Location l => Var l a -> Verifier l expr (SBV a)
symbolVar (Var varLoc) = do
  storedSymbol <- Verifier $ use (varSymbols . at varLoc)

  case storedSymbol of
    Just s -> maybe (Verifier $ throwError (VEMismatchedSymbolType varLoc))
              return
              (s ^? _Symbol)
    Nothing -> do
      newSymbol <- liftSymbolic (symbolic (locationName varLoc))
      Verifier $ varSymbols . at varLoc .= Just (_Symbol # newSymbol)
      return newSymbol

--------------------------------------------------------------------------------
--  Tests
--------------------------------------------------------------------------------

testExpr1 :: Expr BasicOp (Var String) Integer
testExpr1 = EOp (EVar (Var "x") `bMul` EOp (bLit 10))

testExpr2 :: Expr BasicOp (Var String) Integer
testExpr2 = EOp (EVar (Var "x") `bMul` EOp (bLit 5))

testExpr3 :: Expr BasicOp (Var String) Bool
testExpr3 = EOp (testExpr1 `bGT` testExpr2)

testProp :: PropOn (Expr BasicOp (Var String)) Bool
testProp = EVar testExpr3

testVarmap :: Map String (VerifierSymbol Identity)
testVarmap = Map.fromList
  [ ("x", VSInteger 5)
  ]

testGetVar :: (Var String) a -> Maybe a
testGetVar (Var v) = testVarmap ^? at v . _Just . _Symbol . _Wrapped

testProp' :: PropOn (Expr BasicOp Maybe) Bool
testProp' = mapOp (mapOp testGetVar) testProp

testEval :: Maybe Bool
testEval = evalOp (mapOp evalOp testProp')

testVerifier :: Verifier String (Expr BasicOp) Bool
testVerifier = checkProp testProp

test :: IO (Either (VerifierError String (Expr BasicOp)) Bool)
test = runVerifier testVerifier
