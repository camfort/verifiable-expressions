{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE LambdaCase         #-}

module Language.While.Hoare where

import           Control.Applicative   (liftA2)
import           Data.Data

import           Data.Map              (Map)
import qualified Data.Map              as Map

import           Control.Lens

import           Language.While.Syntax


data Prop l
  = PAnd (Prop l) (Prop l)
  | POr (Prop l) (Prop l)
  | PNot (Prop l)
  | PImplies (Prop l) (Prop l)
  | PBexpr (Bexpr l)
  | PTrue
  | PFalse
  deriving (Typeable, Data, Functor, Foldable, Traversable)


bindProp :: (a -> Expr b) -> Prop a -> Prop b
bindProp f = \case
  PAnd p1 p2 -> PAnd (bindProp f p1) (bindProp f p2)
  POr p1 p2 -> POr (bindProp f p1) (bindProp f p2)
  PNot prop -> PNot (bindProp f prop)
  PImplies p1 p2 -> PImplies (bindProp f p1) (bindProp f p2)
  PBexpr bexpr -> PBexpr (bindBexpr f bexpr)
  PTrue -> PTrue
  PFalse -> PFalse


evalProp :: (Ord l, Num n, Ord n) => (l -> Maybe n) -> Prop l -> Maybe Bool
evalProp env = \case
  PAnd p1 p2 -> liftA2 (&&) (evalProp env p1) (evalProp env p2)
  POr p1 p2 -> liftA2 (||) (evalProp env p1) (evalProp env p2)
  PNot prop -> not <$> evalProp env prop
  PImplies p1 p2 -> liftA2 (==>) (evalProp env p1) (evalProp env p2)
    where a ==> b = not a || b
  PBexpr bexpr -> evalBexpr env bexpr
  PTrue -> Just True
  PFalse -> Just False


data PropAnn l a = PropAnn (Prop l) a


type AnnCommand l a = Command l (PropAnn l a)


-- | Check whether the given command is sufficiently annotated to be suitable
-- for automatic Hoare verification.
--
-- This means annotations must be present:
-- - Around C_1 in @C_1; C_2@ if @C_2@ is not an assignment command
-- - Around @C@ in @while B do C@
checkAnnotated :: AnnCommand l a -> Bool
checkAnnotated = \case
  CSeq c (CAssign _ _) -> checkAnnotated c
  CSeq c1 (CAnn _ c2) -> checkAnnotated c1 && checkAnnotated c2
  CSeq _ _ -> False

  CWhile _ (CAnn _ c) -> checkAnnotated c
  CWhile _ _ -> False

  CAnn _ c -> checkAnnotated c
  CSkip -> True
  CAssign _ _ -> True
  CIf _ c1 c2 -> checkAnnotated c1 && checkAnnotated c2


substProp :: (Ord l) => Expr l -> l -> Prop l -> Prop l
substProp expr loc = bindProp (\loc' -> if loc' == loc then expr else EVar loc')


-- | Generate verification conditions to prove that the given Hoare partial
-- correctness triple holds.
generateVcs :: (Ord l) => Prop l -> Prop l -> AnnCommand l a -> Maybe [Prop l]
generateVcs precond postcond = \case
  CAnn (PropAnn prop _) command ->
    generateVcs (prop `PAnd` precond) postcond command

  CSeq command (CAssign loc expr) ->
    generateVcs precond (substProp expr loc postcond) command

  CSeq c1 (CAnn (PropAnn midcond _) c2) ->
    do vcs1 <- generateVcs precond midcond c1
       vcs2 <- generateVcs midcond postcond c2
       return (vcs1 ++ vcs2)

  CSkip -> return [precond `PImplies` postcond]

  CAssign loc expr ->
    return [precond `PImplies` substProp expr loc postcond]

  CIf cond c1 c2 ->
    do vcs1 <- generateVcs (precond `PAnd` PBexpr cond) postcond c1
       vcs2 <- generateVcs (precond `PAnd` PNot (PBexpr cond)) postcond c1
       return (vcs1 ++ vcs2)

  CWhile cond (CAnn (PropAnn invariant _) body) ->
    do let condHolds = PBexpr cond

       invariantMaintained <- generateVcs (condHolds `PAnd` invariant) invariant body

       return ([precond `PImplies` invariant] ++
               [(invariant `PAnd` PNot condHolds) `PImplies` postcond] ++
               invariantMaintained)

  -- If this falls through, the command is not sufficiently annotated
  _ -> Nothing

