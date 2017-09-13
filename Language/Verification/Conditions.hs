{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}

{- |

Combinators for generating verification conditions for programs.

-}
module Language.Verification.Conditions
  (
  -- * Types
    Assignment(..)
  , AnnSeq(..)
  , Triplet

  -- * Generating Verification Conditions
  , skipVCs
  , assignVCs
  , sequenceVCs
  , ifVCs
  , multiIfVCs
  , whileVCs

  -- * Combinators
  , subAssignment
  , chainSub
  , joinAnnSeq
  , JoinAnnSeq(..)
  , joiningAnnSeq
  , emptyAnnSeq
  , propAnnSeq
  , cmdAnnSeq

  -- * Propositions
  , module Language.Expression.Prop
  ) where

import           Data.List                  (intersperse)
import           Data.Monoid                (Endo (..))

import           Control.Monad.Writer       (MonadWriter (tell))

import           Language.Expression.Pretty
import           Language.Expression.Prop
import           Language.Verification

--------------------------------------------------------------------------------
--  Exposed Types
--------------------------------------------------------------------------------

-- | An assignment of a particular expression to a particular variable.
data Assignment expr var where
  Assignment :: var a -> expr var a -> Assignment expr var

instance (Pretty1 var, Pretty2 expr) => Pretty (Assignment expr var) where
  prettysPrec p (Assignment v e) = showParen (p > 9) $
    prettys1Prec 10 v . showString " := " . prettys2Prec 10 e

-- | An annotated sequence. Consists of runs of assignments, with other commands
-- separated by annotations.
data AnnSeq expr var cmd
  = JustAssign [Assignment expr var]
  -- ^ Just a series of assignments without annotations
  | CmdAssign cmd [Assignment expr var]
  -- ^ A command followed by a series of assignments
  | Annotation (AnnSeq expr var cmd) (Prop (expr var) Bool) (AnnSeq expr var cmd)
  -- ^ An initial sequence, followed by an annotation, then another sequence
  deriving (Functor, Foldable, Traversable)

instance (Pretty2 expr, Pretty1 var, Pretty cmd) => Pretty (AnnSeq expr var cmd) where
  prettysPrec _ (JustAssign as)
    = appEndo . mconcat
    . intersperse (Endo (showString "; "))
    . map (Endo . prettysPrec 10)
    $ as

  prettysPrec _ (CmdAssign cmd as)
    =  appEndo . mconcat
      . intersperse (Endo (showString "; "))
      . (Endo (prettysPrec 10 cmd) :)
      . map (Endo . prettysPrec 10)
      $ as

  prettysPrec _ (Annotation l p r)
    = prettysPrec 10 l
    . showString "; {"
    . prettysPrec 10 p
    . showString "}"
    . prettysPrec 10 r

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

-- | Substitutes variables in the given proposition based on the given
-- assignment.
subAssignment
  :: (HMonad expr, VerifiableVar v)
  => Assignment expr v -> Prop (expr v) a -> Prop (expr v) a
subAssignment (Assignment targetVar newExpr) = hmap (^>>= subVar newExpr targetVar)


-- | Chains substitutions, substituting using each assignment in the given list
-- in turn.
chainSub
  :: (HMonad expr, VerifiableVar v)
  => Prop (expr v) Bool -> [Assignment expr v] -> Prop (expr v) Bool
chainSub prop []       = prop
chainSub prop (a : as) = subAssignment a (chainSub prop as)


-- | Joins two annotations together without a Hoare annotation in between. Fails
-- if this would place two non-assignment commands after each other, because
-- these need an annotation.
joinAnnSeq :: AnnSeq expr var cmd -> AnnSeq expr var cmd -> Maybe (AnnSeq expr var cmd)
joinAnnSeq (JustAssign xs) (JustAssign ys) = return $ JustAssign (xs ++ ys)
joinAnnSeq (CmdAssign cmd xs) (JustAssign ys) = return $ CmdAssign cmd (xs ++ ys)
joinAnnSeq s (JustAssign []) = return s
joinAnnSeq (JustAssign []) s = return s
joinAnnSeq (Annotation l p r) r' = Annotation l p <$> joinAnnSeq r r'
joinAnnSeq l' (Annotation l p r) = (\l'' -> Annotation l'' p r) <$> joinAnnSeq l' l
joinAnnSeq _ _ = Nothing


emptyAnnSeq :: AnnSeq expr var cmd
emptyAnnSeq = JustAssign []

propAnnSeq :: Prop (expr var) Bool -> AnnSeq expr var cmd
propAnnSeq p = Annotation emptyAnnSeq p emptyAnnSeq

cmdAnnSeq :: cmd -> AnnSeq expr var cmd
cmdAnnSeq c = CmdAssign c []


-- | 'JoinAnnSeq' forms a 'Monoid' out of 'AnnSeq' by propagating failure to
-- join arising from 'joinAnnSeq'.
newtype JoinAnnSeq expr var cmd = JoinAnnSeq { tryJoinAnnSeq :: Maybe (AnnSeq expr var cmd) }

joiningAnnSeq :: AnnSeq expr var cmd -> JoinAnnSeq expr var cmd
joiningAnnSeq = JoinAnnSeq . Just

instance Monoid (JoinAnnSeq expr var cmd) where
  mempty = JoinAnnSeq (Just emptyAnnSeq)
  mappend (JoinAnnSeq (Just x)) (JoinAnnSeq (Just y)) = JoinAnnSeq (x `joinAnnSeq` y)
  mappend _ _ = JoinAnnSeq Nothing

--------------------------------------------------------------------------------
--  Generating verification conditions
--------------------------------------------------------------------------------

type MonadGenVCs expr var = MonadWriter [Prop (expr var) Bool]

type Triplet expr var a = (Prop (expr var) Bool, Prop (expr var) Bool, a)

-- | Generates verification conditions for a skip statement.
skipVCs
  :: (HMonad expr, MonadGenVCs expr var m)
  => Triplet expr var () -> m ()
skipVCs (precond, postcond, ()) = tell [precond *-> postcond]


-- | Generates verification conditions for an assignment.
assignVCs
  :: (HMonad expr, MonadGenVCs expr v m, VerifiableVar v)
  => Triplet expr v (Assignment expr v) -> m ()
assignVCs (precond, postcond, assignment) = do
  let postcond' = subAssignment assignment postcond
  tell [precond *-> postcond']


-- | Generates verification conditions for a sequence of commands.
sequenceVCs
  :: (HMonad expr, MonadGenVCs expr v m, VerifiableVar v)
  => (Triplet expr v cmd -> m a)
  -> Triplet expr v (AnnSeq expr v cmd) -> m [a]
sequenceVCs cmdVCs (precond, postcond, annSeq) =
  case annSeq of
    -- A sequence of assignments can be verified by checking the precondition
    -- implies the postcondition, after substitutions are performed by the
    -- assignments.
    JustAssign as -> do
      tell [precond *-> chainSub postcond as]
      return []

    -- A command followed by a sequence of assignments can be verified by
    -- substituting based on the assignments in the postcondition, then verifying
    -- the command with the new postcondition and original precondition.
    CmdAssign cmd as ->
      let postcond' = chainSub postcond as
      in (: []) <$> cmdVCs (precond, postcond', cmd)

    -- To verify @{P} C_1 ; {R} C_2 {Q}@, verify @{P} C_1 {R}@ and @{R} C_2 {Q}@.
    Annotation l midcond r -> do
      (++) <$> sequenceVCs cmdVCs (precond, midcond, l)
           <*> sequenceVCs cmdVCs (midcond, postcond, r)


-- | Generates verification conditions for a two-branch if command.
ifVCs
  :: (HMonad expr, MonadGenVCs expr v m)
  => (Triplet expr v cmd -> m a)
  -> (cond -> Prop (expr v) Bool)
  -> Triplet expr v (cond, cmd, cmd) -> m (a, a)
ifVCs cmdVCs condToProp (precond, postcond, (cond, cmd1, cmd2)) = do
  let condProp = condToProp cond
  return (,) <*> cmdVCs ((precond *&& condProp), postcond, cmd1)
             <*> cmdVCs ((precond *&& pnot condProp), postcond, cmd2)


-- | Generates verification conditions for a multi-branch if-then-else-...
-- command.
multiIfVCs
  :: (HMonad expr, Monad m)
  => (Triplet expr v cmd -> m ())
  -> (cond -> Prop (expr v) Bool)
  -> Triplet expr v [(Maybe cond, cmd)] -> m ()
multiIfVCs cmdVCs condToProp (precond, postcond, branches) = go precond branches
  where
    go precond' ((branchCond, branchCmd) : rest) =
      case branchCond of
        Just bc -> do
          let bc' = condToProp bc
          cmdVCs ((precond' *&& bc'), postcond, branchCmd)
          go (precond' *&& pnot bc') rest
        Nothing -> do
          cmdVCs (precond', postcond, branchCmd)
    go _ [] = return ()


-- | Generates verification conditions for a while loop.
whileVCs
  :: (HMonad expr, MonadGenVCs expr v m)
  => (Triplet expr v cmd -> m ())
  -> (cond -> Prop (expr v) Bool)
  -> Prop (expr v) Bool -- ^ Loop invariant
  -> Triplet expr v (cond, cmd) -> m ()
whileVCs cmdVCs condToProp invariant (precond, postcond, (cond, body)) = do
  let condProp = condToProp cond
  -- Assert that the invariant is maintained over the loop body
  cmdVCs ((invariant *&& condProp), invariant, body)
  -- Assert that the invariant is implied by precondition, and at the end of the
  -- loop the invariant implies the postcondition
  tell [precond *-> invariant, (invariant *&& pnot condProp) *-> postcond]
