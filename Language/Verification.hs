{-# LANGUAGE FlexibleContexts #-}

module Language.Verification
  (
  -- * The verification monad
    Verifier
  , runVerifier
  , runVerifierWith
  , VerifierError(..)

  -- * The query monad
  , Query
  , query

  -- * Verifiable types and variables
  , VerifierSymbol
  , Verifiable(..)
  , Location(..)
  , Var(..)

  -- * Verifier actions
  , checkProp

  -- * Miscellaneous combinators
  , subVar
  , propToSBV
  ) where

import           Control.Monad.Except

import           Data.SBV                      (SBV, SBool, bnot, constrain)
import qualified Data.SBV.Control              as S

import           Language.Expression
import           Language.Expression.DSL
import           Language.Expression.SBV
import           Language.Verification.Core

--------------------------------------------------------------------------------
--  Query actions
--------------------------------------------------------------------------------

checkProp
  :: (Substitutive expr, Location l, EvalOp (EvalT EvalContext (Query l expr)) SBV expr)
  => PropOver (expr (Var l)) Bool
  -> Query l expr Bool
checkProp prop = do
  symbolicProp <- propToSBV defaultEvalContext prop
  liftSymbolic . S.query $ do
    constrain (bnot symbolicProp)
    cs <- S.checkSat
    case cs of
      S.Unsat -> return True
      _ -> return False

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

propToSBV
  :: (Substitutive expr, Location l, EvalOp (EvalT EvalContext (Query l expr)) SBV expr)
  => EvalContext
  -> PropOver (expr (Var l)) Bool
  -> Query l expr SBool
propToSBV context prop = do
  res <- runEvalT (evalOp (evalOp (lift . symbolVar)) prop) context
  either (throwError . VEEval) return res
