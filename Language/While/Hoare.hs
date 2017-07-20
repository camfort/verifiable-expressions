{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE LambdaCase         #-}

module Language.While.Hoare where

import           Control.Applicative   (liftA2)
import           Data.Data
import Debug.Trace

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


data PropAnn l a = PropAnn (Prop l) a
  deriving (Show, Functor, Foldable, Traversable)


type AnnCommand l a = Command l (PropAnn l a)


-- | Split the command into all the top-level sequenced commands.
-- E.g.
--
-- @splitSeq (a `CSeq` b `CSeq` c) == [a, b, c]@
-- (if none of @a@, @b@ or @c@ is a sequence itself; in that case they would be
-- further subdivided).
splitSeq :: Command l a -> [Command l a]
splitSeq = \case
  CSeq c1 c2 -> splitSeq c1 ++ splitSeq c2
  c -> [c]


data AnnSeq l a
  = Assignments [(l, Expr l)]
  | Annotation (AnnSeq l a) [Prop l] (AnnCommand l a) [(l, Expr l)]
  deriving (Show)


joinAnn :: AnnSeq l a -> AnnSeq l a -> AnnSeq l a
joinAnn (Assignments xs) (Assignments ys) = Assignments (xs ++ ys)
joinAnn (Annotation s p c xs) (Assignments ys) = Annotation s p c (xs ++ ys)
joinAnn r (Annotation s p c xs) = Annotation (r `joinAnn` s) p c xs


joinWithMidcond :: AnnSeq l a -> Prop l -> AnnSeq l a -> Maybe (AnnSeq l a)
joinWithMidcond (Assignments xs) midcond (Assignments ys)
  | (loc, expr) : yss <- ys = Just (Annotation (Assignments xs) [midcond] (CAssign loc expr) yss)
  | otherwise = Nothing
joinWithMidcond (Annotation s p c xs) midcond (Assignments ys) =
  Just (Annotation s (midcond : p) c (xs ++ ys))
joinWithMidcond r midcond (Annotation s p c xs) =
  do t <- joinWithMidcond r midcond s
     return (Annotation t p c xs)


-- | Split the command into all the top-level sequenced commands, interspersed
-- with annotations. Returns 'Nothing' if the command's sequences are not
-- sufficiently annotated.
splitSeq' :: AnnCommand l a -> Maybe (AnnSeq l a)
splitSeq' = \case
  CSeq c1 (CAnn (PropAnn midcond _) c2) ->
    do a1 <- splitSeq' c1
       a2 <- splitSeq' c2
       joinWithMidcond a1 midcond a2
  CSeq c1 (CAssign loc expr) ->
    do a1 <- splitSeq' c1
       return $ a1 `joinAnn` Assignments [(loc, expr)]
  CSeq c1 c2 ->
    do a1 <- splitSeq' c1
       a2 <- splitSeq' c2
       return $ a1 `joinAnn` a2
  CAssign loc expr -> return $ Assignments [(loc, expr)]
  c -> return $ SingleCommand c


substProp :: (Ord l) => Expr l -> l -> Prop l -> Prop l
substProp expr loc = bindProp (\loc' -> if loc' == loc then expr else EVar loc')


seqMany :: Command l a -> [Command l a] -> Command l a
seqMany c [] = c
seqMany c (c1 : cs) = CSeq c (seqMany c1 cs)


chainSub :: (Ord l) => Prop l -> [(l, Expr l)] -> Prop l
chainSub prop [] = prop
chainSub prop ((loc, expr) : xs) =
  substProp expr loc (chainSub prop xs)


andProps :: [Prop l] -> Prop l
andProps [] = PTrue
andProps [x] = x
andProps (x : xs) = x `PAnd` andProps xs


seqVcs :: (Ord l, Show a, Show l) => Prop l -> Prop l -> AnnSeq l a -> Maybe [Prop l]
seqVcs precond postcond = \case
  Assignments xs -> Just [precond `PImplies` chainSub postcond xs]
  Annotation s ps command xs ->
    do let midcond = andProps ps
       former <- seqVcs precond midcond s
       latter <- generateVcs midcond (chainSub postcond xs) command
       return (former ++ latter)


-- | Generate verification conditions to prove that the given Hoare partial
-- correctness triple holds.
generateVcs :: (Ord l, Show a, Show l) => Prop l -> Prop l -> AnnCommand l a -> Maybe [Prop l]
generateVcs precond postcond = \case
  CAnn (PropAnn prop _) command ->
    generateVcs (prop `PAnd` precond) postcond command

  c@(CSeq _ _) ->
    do seq <- splitSeq' c
       traceShowM seq
       seqVcs precond postcond seq

  CSkip -> return [precond `PImplies` postcond]

  CAssign loc expr ->
    return [precond `PImplies` substProp expr loc postcond]

  CIf cond c1 c2 ->
    do vcs1 <- generateVcs (precond `PAnd` PBexpr cond) postcond c1
       vcs2 <- generateVcs (precond `PAnd` PNot (PBexpr cond)) postcond c1
       return (vcs1 ++ vcs2)

  CWhile cond (CAnn (PropAnn invariant _) body) ->
    do let condHolds = PBexpr cond

       invariantMaintained <- generateVcs (invariant `PAnd` condHolds) invariant body

       return ([precond `PImplies` invariant] ++
               [(invariant `PAnd` PNot condHolds) `PImplies` postcond] ++
               invariantMaintained)

  -- If this falls through, the command is not sufficiently annotated
  _ -> Nothing

