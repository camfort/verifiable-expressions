{-# LANGUAGE LambdaCase #-}

module Language.While.Hoare.Prover where

import qualified Language.Expression           as V
import           Language.Expression.DSL
import qualified Language.Expression.Operators as V
import           Language.Verification

import           Language.While.Hoare


checkPartialHoare
  :: Location l
  => WhileProp l
  -> WhileProp l
  -> AnnCommand l a
  -> Query l (V.Expr' V.StandardOps) Bool
checkPartialHoare precond postcond cmd =
  do vcs <- case generateVCs precond postcond cmd of
              Just x -> return x
              Nothing -> fail "Command not sufficiently annotated"

     let bigVC = foldr (*&&) (plit True) vcs

     checkProp bigVC

provePartialHoare
  :: Location l
  => WhileProp l
  -> WhileProp l
  -> AnnCommand l a
  -> IO (Either (VerifierError l (V.Expr' V.StandardOps)) Bool)
provePartialHoare precond postcond cmd =
  runVerifier . query $ checkPartialHoare precond postcond cmd
