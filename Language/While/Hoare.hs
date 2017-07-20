{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE LambdaCase         #-}

module Language.While.Hoare where

import           Control.Applicative   (liftA2)
import           Data.Data

import           Language.While.Syntax


--------------------------------------------------------------------------------
--  Exposed Data Types
--------------------------------------------------------------------------------

data Prop l
  = PAnd (Prop l) (Prop l)
  | POr (Prop l) (Prop l)
  | PNot (Prop l)
  | PImplies (Prop l) (Prop l)
  | PBexpr (Bexpr l)
  | PTrue
  | PFalse
  deriving (Show, Data, Typeable, Functor, Foldable, Traversable)


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


substProp :: (Ord l) => Expr l -> l -> Prop l -> Prop l
substProp expr loc = bindProp (\loc' -> if loc' == loc then expr else EVar loc')


data PropAnn l a = PropAnn (Prop l) a
  deriving (Show, Functor, Foldable, Traversable)


type AnnCommand l a = Command l (PropAnn l a)

--------------------------------------------------------------------------------
--  Exposed Functions
--------------------------------------------------------------------------------

-- | Generate verification conditions to prove that the given Hoare partial
-- correctness triple holds.
generateVcs :: (Ord l) => Prop l -> Prop l -> AnnCommand l a -> Maybe [Prop l]
generateVcs precond postcond = \case
  CAnn (PropAnn prop _) command ->
    generateVcs (prop `PAnd` precond) postcond command

  c@(CSeq _ _) -> splitSeq c >>= seqVcs precond postcond

  CSkip -> return [precond `PImplies` postcond]

  CAssign loc expr ->
    return [precond `PImplies` substProp expr loc postcond]

  CIf cond c1 c2 ->
    do vcs1 <- generateVcs (precond `PAnd` PBexpr cond) postcond c1
       vcs2 <- generateVcs (precond `PAnd` PNot (PBexpr cond)) postcond c2
       return (vcs1 ++ vcs2)

  CWhile cond (CAnn (PropAnn invariant _) body) ->
    do let condHolds = PBexpr cond

       invariantMaintained <- generateVcs (invariant `PAnd` condHolds) invariant body

       return ([precond `PImplies` invariant] ++
               [(invariant `PAnd` PNot condHolds) `PImplies` postcond] ++
               invariantMaintained)

  -- If this falls through, the command is not sufficiently annotated
  _ -> Nothing

--------------------------------------------------------------------------------
--  Internal
--------------------------------------------------------------------------------

-- | An annotated sequence. Consists of runs of assignments, with other commands
-- separated by annotations.
data AnnSeq l a
  = JustAssign [(l, Expr l)]
  | CmdAssign (AnnCommand l a) [(l, Expr l)]
  | Annotation (AnnSeq l a) (Prop l) (AnnSeq l a)
  deriving (Show)

-- | Generates the verification conditions for a sequence of commands
-- interspersed with annotations.
seqVcs :: (Ord l) => Prop l -> Prop l -> AnnSeq l a -> Maybe [Prop l]
seqVcs precond postcond = \case
  -- A sequence of assignments can be verified by checking the precondition
  -- implies the postcondition, after substitutions are performed by the
  -- assignments.
  JustAssign xs -> Just [precond `PImplies` chainSub postcond xs]

  -- A command followed by a sequence of assignments can be verified by
  -- substituting based on the assignments in the postcondition, then verifying
  -- the command with the new postcondition and original precondition.
  CmdAssign c xs ->
    let postcond' = chainSub postcond xs
    in generateVcs precond postcond' c

  -- To verify @{P} C_1 ; {R} C_2 {Q}@, verify @{P} C_1 {R}@ and @{R} C_2 {Q}@.
  Annotation l midcond r ->
    do vcsL <- seqVcs precond midcond l
       vcsR <- seqVcs midcond postcond r
       return (vcsL ++ vcsR)


-- | Performs substitutions in a proposition from a chain of assignments.
chainSub :: (Ord l) => Prop l -> [(l, Expr l)] -> Prop l
chainSub prop [] = prop
chainSub prop ((loc, expr) : xs) =
  substProp expr loc (chainSub prop xs)


-- | Joins two annotations together without a Hoare annotation in between. Fails
-- if this would place two non-assignment commands after each other, because
-- these need an annotation.
joinAnn :: AnnSeq l a -> AnnSeq l a -> Maybe (AnnSeq l a)
joinAnn (JustAssign xs) (JustAssign ys) = return $ JustAssign (xs ++ ys)
joinAnn (JustAssign []) s@(CmdAssign _ _) = return s
joinAnn (Annotation l p r) r' = Annotation l p <$> joinAnn r r'
joinAnn l' (Annotation l p r) = joinAnn l' l >>= \l'' -> return $ Annotation l'' p r
joinAnn _ _ = Nothing


-- | Split the command into all the top-level sequenced commands, interspersed
-- with annotations. Returns 'Nothing' if the command's sequences are not
-- sufficiently annotated.
splitSeq :: AnnCommand l a -> Maybe (AnnSeq l a)
splitSeq = \case
  CSeq c1 (CAnn (PropAnn midcond _) c2) ->
    do a1 <- splitSeq c1
       a2 <- splitSeq c2
       return $ Annotation a1 midcond a2
  CSeq c1 (CAssign loc expr) ->
    do a1 <- splitSeq c1
       a1 `joinAnn` JustAssign [(loc, expr)]
  CSeq c1 c2 ->
    do a1 <- splitSeq c1
       a2 <- splitSeq c2
       a1 `joinAnn` a2
  CAssign loc expr -> return $ JustAssign [(loc, expr)]
  c -> return $ CmdAssign c []
