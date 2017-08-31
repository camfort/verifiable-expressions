{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeFamilies     #-}

module Language.While.Hoare.Prover where

import           Data.SBV                (SBV)

import           Language.Expression.Prop
import           Language.Verification

import           Language.While.Hoare
import           Language.While.Syntax


checkPartialHoare
  :: (VerifiableVar (WhileVar l), VarSym (WhileVar l) ~ SBV)
  => WhileProp l Bool
  -> WhileProp l Bool
  -> AnnCommand l a
  -> Query (WhileVar l) (SBV Bool)
checkPartialHoare precond postcond cmd =
  do vcs <- case generateVCs precond postcond cmd of
              Just x  -> return x
              Nothing -> fail "Command not sufficiently annotated"

     let bigVC = foldr (*&&) (plit True) vcs

     checkProp bigVC

provePartialHoare
  :: (VerifiableVar (WhileVar l), VarSym (WhileVar l) ~ SBV)
  => WhileProp l Bool
  -> WhileProp l Bool
  -> AnnCommand l a
  -> IO (Either (VerifierError (WhileVar l)) Bool)
provePartialHoare precond postcond cmd =
  runVerifier . query $ checkPartialHoare precond postcond cmd
