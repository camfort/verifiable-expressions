{-# LANGUAGE LambdaCase #-}

module Language.While.Hoare.Prover where

import           Data.Functor.Identity (Identity (..))

import qualified Data.Map              as Map
import           Data.Set              (Set)

import           Control.Lens
import           Data.Set.Lens

import           Data.SBV              (Boolean (..), EqSymbolic (..),
                                        OrdSymbolic (..), SBool, SInteger,
                                        Symbolic, bAnd, isTheorem, sInteger)

import           Language.While.Hoare
import           Language.While.Prop   as P
import           Language.While.Syntax as S


symbolicExpr :: Expr SInteger -> Maybe SInteger
symbolicExpr = evalExpr Just


evalArithOp' :: (OrdSymbolic n) => ArithOp n -> SBool
evalArithOp' = \case
  OLess a b -> a .< b
  OLessEq a b -> a .<= b
  OEq a b -> a .== b


evalBoolOp' :: (Boolean b) => BoolOp b -> b
evalBoolOp' = \case
  S.OAnd a b -> a &&& b
  S.OOr a b -> a ||| b
  S.ONot a -> bnot a


evalPropOp :: (Boolean b) => PropOp b -> b
evalPropOp =
  let impl a b = bnot a ||| b
  in \case
    P.OAnd a b -> a &&& b
    P.OOr a b -> a ||| b
    P.OImpl a b -> a `impl` b
    P.OEquiv a b -> (a `impl` b) &&& (b `impl` a)
    P.ONot a -> bnot a


evalSymbProp :: WhileProp SInteger -> SBool
evalSymbProp
  = runIdentity
  . evalPropGeneral
      evalPropOp
      fromBool
      (evalBexprGeneral evalArithOp' evalBoolOp' pure)


symbolicVars :: [WhileProp String] -> Symbolic [WhileProp SInteger]
symbolicVars props = do
  let
    freeVars :: Set String
    freeVars = setOf (traverse . traverse . traverse) props

  symbolAssoc <-
    traverse (\name -> sInteger name >>= \symbol -> return (name, symbol))
             (freeVars ^.. folded)

  let symbolMap = Map.fromList symbolAssoc

      result :: Maybe [WhileProp SInteger]
      result = props & traverse . traverse . traverse %%~ (`Map.lookup` symbolMap)

  case result of
    Just r -> return r
    Nothing -> error "unreachable"


vcsToSBool :: [WhileProp SInteger] -> SBool
vcsToSBool = bAnd . map evalSymbProp


generateSymbolicVcs :: WhileProp String -> WhileProp String -> AnnCommand String a -> Maybe (Symbolic SBool)
generateSymbolicVcs precond postcond command =
  do vcs <- generateVcs precond postcond command
     let symbolicVcs = symbolicVars vcs
     return (vcsToSBool <$> symbolicVcs)


provePartialHoare :: WhileProp String -> WhileProp String -> AnnCommand String a -> IO Bool
provePartialHoare precond postcond command =
  do vcs <- case generateSymbolicVcs precond postcond command of
       Just v -> return v
       Nothing -> fail "Command not sufficiently annotated"
     isTheorem vcs
