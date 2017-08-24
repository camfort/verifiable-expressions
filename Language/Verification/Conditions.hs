{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE UndecidableInstances   #-}

{- |

Combinators for generating verification conditions for programs.

-}
module Language.Verification.Conditions
  (
  -- * Types
    Prop
  , Assignment(..)
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
  ) where

import           Control.Monad.Writer    (MonadWriter (tell))

import           Language.Expression.DSL hiding (Prop)
import           Language.Verification

--------------------------------------------------------------------------------
--  Exposed Types
--------------------------------------------------------------------------------

-- | A proposition over expressions in the language.
type Prop (expr :: (* -> *) -> * -> *) var = PropOver (expr var) Bool

-- | An assignment of a particular expression to a particular variable.
data Assignment expr var where
  Assignment :: var a -> expr var a -> Assignment expr var

-- | An annotated sequence. Consists of runs of assignments, with other commands
-- separated by annotations.
data AnnSeq expr var cmd
  = JustAssign [Assignment expr var]
  -- ^ Just a series of assignments without annotations
  | CmdAssign cmd [Assignment expr var]
  -- ^ A command followed by a series of assignments
  | Annotation (AnnSeq expr var cmd) (PropOver (expr var) Bool) (AnnSeq expr var cmd)
  -- ^ An initial sequence, followed by an annotation, then another sequence

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

-- | Substitutes variables in the given proposition based on the given
-- assignment.
subAssignment
  :: (Substitutive expr, VerifiableVar v)
  => Assignment expr v -> PropOver (expr v) a -> PropOver (expr v) a
subAssignment (Assignment targetVar newExpr) = hmapOp (bindVars' (subVar newExpr targetVar))


-- | Chains substitutions, substituting using each assignment in the given list
-- in turn.
chainSub
  :: (Substitutive expr, VerifiableVar v)
  => Prop expr v -> [Assignment expr v] -> Prop expr v
chainSub prop []       = prop
chainSub prop (a : as) = subAssignment a (chainSub prop as)

-- | Joins two annotations together without a Hoare annotation in between. Fails
-- if this would place two non-assignment commands after each other, because
-- these need an annotation.
joinAnnSeq :: AnnSeq expr var cmd -> AnnSeq expr var cmd -> Maybe (AnnSeq expr var cmd)
joinAnnSeq (JustAssign xs) (JustAssign ys) = return $ JustAssign (xs ++ ys)
joinAnnSeq (CmdAssign cmd xs) (JustAssign ys) = return $ CmdAssign cmd (xs ++ ys)
joinAnnSeq (JustAssign []) s@(CmdAssign _ _) = return s
joinAnnSeq (Annotation l p r) r' = Annotation l p <$> joinAnnSeq r r'
joinAnnSeq l' (Annotation l p r) = joinAnnSeq l' l >>= \l'' -> return $ Annotation l'' p r
joinAnnSeq _ _ = Nothing

emptyAnnSeq :: AnnSeq expr var cmd
emptyAnnSeq = JustAssign []

propAnnSeq :: PropOver (expr var) Bool -> AnnSeq expr var cmd
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

class MonadWriter [Prop expr var] m => MonadGenVCs expr var m | m -> expr var
instance MonadWriter [Prop expr var] m => MonadGenVCs expr var m

type Triplet expr var a = (Prop expr var, Prop expr var, a)

-- | Generates verification conditions for a skip statement.
skipVCs
  :: (Substitutive expr, MonadGenVCs expr var m)
  => Triplet expr var () -> m ()
skipVCs (precond, postcond, ()) = tell [precond *-> postcond]


-- | Generates verification conditions for an assignment.
assignVCs
  :: (Substitutive expr, MonadGenVCs expr v m, VerifiableVar v)
  => Triplet expr v (Assignment expr v) -> m ()
assignVCs (precond, postcond, assignment) = do
  let postcond' = subAssignment assignment postcond
  tell [precond *-> postcond']


-- | Generates verification conditions for a sequence of commands.
sequenceVCs
  :: (Substitutive expr, MonadGenVCs expr v m, VerifiableVar v)
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
  :: (Substitutive expr, MonadGenVCs expr v m)
  => (Triplet expr v cmd -> m a)
  -> (cond -> Prop expr v)
  -> Triplet expr v (cond, cmd, cmd) -> m (a, a)
ifVCs cmdVCs condToProp (precond, postcond, (cond, cmd1, cmd2)) = do
  let condProp = condToProp cond
  return (,) <*> cmdVCs ((precond *&& condProp), postcond, cmd1)
             <*> cmdVCs ((precond *&& pnot condProp), postcond, cmd2)


-- | Generates verification conditions for a multi-branch if-then-else-...
-- command.
multiIfVCs
  :: (Substitutive expr, Monad m)
  => (Triplet expr v cmd -> m ())
  -> (cond -> Prop expr v)
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
  :: (Substitutive expr, MonadGenVCs expr v m)
  => (Triplet expr v cmd -> m ())
  -> (cond -> Prop expr v)
  -> Prop expr v -- ^ Loop invariant
  -> Triplet expr v (cond, cmd) -> m ()
whileVCs cmdVCs condToProp invariant (precond, postcond, (cond, body)) = do
  let condProp = condToProp cond
  -- Assert that the invariant is maintained over the loop body
  cmdVCs ((invariant *&& condProp), invariant, body)
  -- Assert that the invariant is implied by precondition, and at the end of the
  -- loop the invariant implies the postcondition
  tell [precond *-> invariant, (invariant *&& pnot condProp) *-> postcond]
