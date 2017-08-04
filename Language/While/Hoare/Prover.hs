{-# LANGUAGE LambdaCase #-}

module Language.While.Hoare.Prover where

import           Language.Expression.DSL
import           Language.Verification

import           Language.While.Syntax
import           Language.While.Hoare


checkPartialHoare
  :: Location l
  => WhileProp l Bool
  -> WhileProp l Bool
  -> AnnCommand l a
  -> Query l (Expr WhileOp) Bool
checkPartialHoare precond postcond cmd =
  do vcs <- case generateVCs precond postcond cmd of
              Just x -> return x
              Nothing -> fail "Command not sufficiently annotated"

     let bigVC = foldr (*&&) (plit True) vcs

     checkProp bigVC

provePartialHoare
  :: Location l
  => WhileProp l Bool
  -> WhileProp l Bool
  -> AnnCommand l a
  -> IO (Either (VerifierError l (Expr WhileOp)) Bool)
provePartialHoare precond postcond cmd =
  runVerifier . query $ checkPartialHoare precond postcond cmd
