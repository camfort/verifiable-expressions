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

  -- * Verifiable variables
  , VerifiableVar(..)

  -- * Verifier actions
  , checkProp
  , checkPropWith

  -- * Miscellaneous combinators
  , subVar

  -- * Expressions
  , module Expression

  -- * SBV re-exports
  , SMTConfig(..)
  , defaultSMTCfg
  ) where

import           Data.SBV                   (SMTConfig (..), defaultSMTCfg)

import           Language.Expression        as Expression
import           Language.Verification.Core
