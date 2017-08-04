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

  -- * Unknown type
  , Unknown
  ) where

import           Data.SBV                      (SMTConfig (..), SymWord,
                                                defaultSMTCfg)

import           Language.Expression.DSL       as DSL
import           Language.Expression.Operators as Operators
import           Language.Expression.Unknown
import           Language.Verification.Core
