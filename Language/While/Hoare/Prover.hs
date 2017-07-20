{-# LANGUAGE LambdaCase #-}

module Language.While.Hoare.Prover where

import           Control.Applicative   (liftA2)
import           Data.Data
import           Data.Maybe            (fromJust)

import           Data.Map              (Map)
import qualified Data.Map              as Map
import           Data.Set              (Set)
import qualified Data.Set              as Set

import           Control.Lens
import           Data.Data.Lens
import           Data.Set.Lens

import           Data.SBV

import           Language.While.Hoare
import           Language.While.Syntax

symbolicExpr :: Expr SInteger -> Maybe SInteger
symbolicExpr = evalExpr Just


evalBexpr' :: (Num n, OrdSymbolic n) => (l -> Maybe n) -> Bexpr l -> Maybe SBool
evalBexpr' env = \case
  BLess e1 e2 -> liftA2 (.<) (evalExpr env e1) (evalExpr env e2)
  BLessEq e1 e2 -> liftA2 (.<=) (evalExpr env e1) (evalExpr env e2)
  BEq e1 e2 -> liftA2 (.==) (evalExpr env e1) (evalExpr env e2)
  BAnd b1 b2 -> liftA2 (&&&) (evalBexpr' env b1) (evalBexpr' env b2)
  BOr b1 b2 -> liftA2 (|||) (evalBexpr' env b1) (evalBexpr' env b2)
  BNot bexpr -> bnot <$> evalBexpr' env bexpr


symbolicBexpr :: Bexpr SInteger -> Maybe SBool
symbolicBexpr = evalBexpr' Just


propToSBool :: Prop SInteger -> Maybe SBool
propToSBool = \case
  PAnd p1 p2 -> liftA2 (&&&) (propToSBool p1) (propToSBool p2)
  POr p1 p2 -> liftA2 (|||) (propToSBool p1) (propToSBool p2)
  PNot prop -> bnot <$> propToSBool prop
  PImplies p1 p2 -> liftA2 implies (propToSBool p1) (propToSBool p2)
    where implies a b = bnot a ||| b
  PBexpr bexpr -> symbolicBexpr bexpr
  PTrue -> return true
  PFalse -> return false


symbolicVars :: [Prop String] -> Symbolic [Prop SInteger]
symbolicVars props = do
  let
    freeVars :: Set String
    freeVars = setOf (traverse . traverse) props

  symbolAssoc <-
    traverse (\name -> sInteger name >>= \symbol -> return (name, symbol))
             (freeVars ^.. folded)

  let symbolMap = Map.fromList symbolAssoc

      result :: Maybe [Prop SInteger]
      result = props & traverse . traverse %%~ (`Map.lookup` symbolMap)

  case result of
    Just r -> return r
    Nothing -> error "unreachable"


vcsToSBool :: [Prop SInteger] -> Maybe SBool
vcsToSBool = fmap bAnd . traverse propToSBool

generateSymbolicVcs :: (Show a) => Prop String -> Prop String -> AnnCommand String a -> Symbolic SBool
generateSymbolicVcs precond postcond command =
  do vcs <- case generateVcs precond postcond command of
       Just v -> return v
       Nothing -> fail "Command not properly annotated"

     let symbolicVcs = symbolicVars vcs
     fromJust . vcsToSBool <$> symbolicVcs

provePartialHoare :: (Show a) => Prop String -> Prop String -> AnnCommand String a -> IO (Maybe Bool)
provePartialHoare precond postcond command =
  isTheorem (Just 20) (generateSymbolicVcs precond postcond command)
