{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-|

Strongly-typed utilities to aid in automatic verification (e.g. of programs)
using an SMT solver.

This is mainly just a wrapper around "Data.SBV" that allows for inspection and
manipulation of symbolic values, especially variable substitution.

-}
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
  , checkPropWith

  -- * Miscellaneous combinators
  , subVar
  , propToSBV

  -- * Expression DSL
  , module DSL

  -- * Expressions and standard operators
  , module Operators

  -- * SBV re-exports
  , SMTConfig(..)
  , defaultSMTCfg
  , SymWord
  ) where

import           Control.Monad.Except

import           Data.SBV                      (SBV, SBool, SMTConfig (..),
                                                SymWord, bnot, constrain,
                                                defaultSMTCfg)
import qualified Data.SBV.Control              as S

import           Language.Expression.Dict      (BooleanDict, HasDicts)
import           Language.Expression.DSL       as DSL
import           Language.Expression.Operators as Operators
import           Language.Expression.SBV
import           Language.Verification.Core

--------------------------------------------------------------------------------
--  Query actions
--------------------------------------------------------------------------------

-- | Check a proposition, given an environment containing the instances needed
-- to evaluate it symbolically.
checkPropWith
  :: (Substitutive expr, Location l,
      EvalOp (EvalT ctx (Query l expr)) SBV expr,
      HasDicts BooleanDict ctx)
  => ctx
  -> PropOver (expr (Var l)) Bool
  -> Query l expr Bool
checkPropWith ctx prop = do
  symbolicProp <- propToSBV ctx prop
  liftSymbolic . S.query $ do
    constrain (bnot symbolicProp)
    cs <- S.checkSat
    case cs of
      S.Unsat -> return True
      _ -> return False

-- | Check a proposition by evaluating it symbolically (with the default
-- standard environment) and sending it to the SMT solver.
checkProp
  :: (Substitutive expr, Location l, EvalOp (EvalT EvalContext (Query l expr)) SBV expr)
  => PropOver (expr (Var l)) Bool
  -> Query l expr Bool
checkProp = checkPropWith defaultEvalContext

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

propToSBV
  :: (Substitutive expr, Location l, EvalOp (EvalT ctx (Query l expr)) SBV expr,
      HasDicts BooleanDict ctx)
  => ctx
  -> PropOver (expr (Var l)) Bool
  -> Query l expr SBool
propToSBV context prop = do
  res <- runEvalT (evalOp (evalOp (lift . symbolVar)) prop) context
  either (throwError . VEEval) return res
