{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

{- |

Combinators for generating verification conditions for programs.

-}
module Language.Verification.Conditions
  (
  -- * Types
    Prop
  , Assignment(..)
  , AnnSeq(..)
  , GenVCs
  -- * Generating Verification Conditions
  , skipVCs
  , assignVCs
  , sequenceVCs
  , ifVCs
  , whileVCs
  -- * Combinators
  , pNot
  , pAnd
  , pOr
  , pImpl
  , subAssignment
  ) where

import           Language.Verification
import           Language.Verification.Expression
import           Language.Verification.Expression.Operators


--------------------------------------------------------------------------------
--  Exposed Types
--------------------------------------------------------------------------------

-- | A proposition over expressions in the language.
type Prop (expr :: (* -> *) -> * -> *) var = PropOn (expr var) Bool

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
  | Annotation (AnnSeq expr var cmd) (PropOn (expr var) Bool) (AnnSeq expr var cmd)
  -- ^ An initial sequence, followed by an annotation, then another sequence

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

pNot :: PropOn expr Bool -> PropOn expr Bool
pNot x = EOp (OpNot x)

pAnd :: PropOn expr Bool -> PropOn expr Bool -> PropOn expr Bool
pAnd x y = EOp (OpAnd x y)

pOr :: PropOn expr Bool -> PropOn expr Bool -> PropOn expr Bool
pOr x y = EOp (OpOr x y)

pImpl :: PropOn expr Bool -> PropOn expr Bool -> PropOn expr Bool
pImpl x y = pNot x `pOr` y

-- | Substitutes variables in the given proposition based on the given
-- assignment.
subAssignment :: (Substitutive expr) => Assignment expr Var -> PropOn (expr Var) a -> PropOn (expr Var) a
subAssignment (Assignment targetVar newExpr) = mapOp (bindVars (subVar newExpr targetVar))

--------------------------------------------------------------------------------
--  Generating verification conditions
--------------------------------------------------------------------------------

-- | A function that generates verification conditions from something of type
-- 'a', given a precondition and a postcondition.
type GenVCs f expr var a = a -> Prop expr var -> Prop expr var -> f [Prop expr var]

-- | Generates verification conditions for a skip statement.
skipVCs
  :: (Substitutive expr, Applicative f)
  => GenVCs f expr Var ()
skipVCs () precond postcond = pure [precond `pImpl` postcond]


-- | Generates verification conditions for an assignment.
assignVCs
  :: (Substitutive expr, Applicative f)
  => GenVCs f expr Var (Assignment expr Var)
assignVCs assignment precond postcond =
  let postcond' = subAssignment assignment postcond
  in pure [precond `pImpl` postcond']


-- | Generates verification conditions for a sequence of commands.
sequenceVCs
  :: (Substitutive expr, Applicative f)
  => GenVCs f expr Var cmd
  -> GenVCs f expr Var (AnnSeq expr Var cmd)
sequenceVCs cmdVCs annSeq precond postcond =
  case annSeq of
    -- A sequence of assignments can be verified by checking the precondition
    -- implies the postcondition, after substitutions are performed by the
    -- assignments.
    JustAssign as ->
      pure [precond `pImpl` chainSub postcond as]

    -- A command followed by a sequence of assignments can be verified by
    -- substituting based on the assignments in the postcondition, then verifying
    -- the command with the new postcondition and original precondition.
    CmdAssign cmd as ->
      let postcond' = chainSub postcond as
      in cmdVCs cmd precond postcond'

    -- To verify @{P} C_1 ; {R} C_2 {Q}@, verify @{P} C_1 {R}@ and @{R} C_2 {Q}@.
    Annotation l midcond r ->
      (++) <$> sequenceVCs cmdVCs l precond midcond
           <*> sequenceVCs cmdVCs r midcond postcond


-- | Generates verification conditions for a two-branch if command.
ifVCs
  :: (Substitutive expr, Applicative f)
  => GenVCs f expr Var cmd
  -> (cond -> Prop expr Var)
  -> GenVCs f expr Var (cond, cmd, cmd)
ifVCs cmdVCs condToProp (cond, cmd1, cmd2) precond postcond =
  let condProp = condToProp cond
  in (++) <$> cmdVCs cmd1 (precond `pAnd` condProp) postcond
          <*> cmdVCs cmd2 (precond `pAnd` pNot condProp) postcond


-- | Generates verification conditions for a while loop.
whileVCs
  :: (Substitutive expr, Applicative f)
  => GenVCs f expr Var cmd
  -> (cond -> Prop expr Var)
  -> Prop expr Var -- ^ Loop invariant
  -> GenVCs f expr Var (cond, cmd)
whileVCs cmdVCs condToProp invariant (cond, body) precond postcond =
  let condProp = condToProp cond
      invariantMaintained = cmdVCs body (invariant `pAnd` condProp) invariant
      invariantWorks = [precond `pImpl` invariant, (invariant `pAnd` pNot condProp) `pImpl` postcond]
  in (invariantWorks ++) <$> invariantMaintained


--------------------------------------------------------------------------------
--  Internal Functions
--------------------------------------------------------------------------------

chainSub :: (Substitutive expr) => Prop expr Var -> [Assignment expr Var] -> Prop expr Var
chainSub prop [] = prop
chainSub prop (a : as) = subAssignment a (chainSub prop as)
