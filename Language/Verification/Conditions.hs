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
  , pIff
  , subAssignment
  , chainSub
  , joinAnn
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

pIff :: PropOn expr Bool -> PropOn expr Bool -> PropOn expr Bool
pIff x y = (x `pImpl` y) `pAnd` (y `pImpl` x)


-- | Substitutes variables in the given proposition based on the given
-- assignment.
subAssignment
  :: (Substitutive expr, Location l)
  => Assignment expr (Var l) -> PropOn (expr (Var l)) a -> PropOn (expr (Var l)) a
subAssignment (Assignment targetVar newExpr) = mapOp (bindVars (subVar newExpr targetVar))


-- | Chains substitutions, substituting using each assignment in the given list
-- in turn.
chainSub
  :: (Substitutive expr, Location l)
  => Prop expr (Var l) -> [Assignment expr (Var l)] -> Prop expr (Var l)
chainSub prop [] = prop
chainSub prop (a : as) = subAssignment a (chainSub prop as)

-- | Joins two annotations together without a Hoare annotation in between. Fails
-- if this would place two non-assignment commands after each other, because
-- these need an annotation.
joinAnn :: AnnSeq expr var cmd -> AnnSeq expr var cmd -> Maybe (AnnSeq expr var cmd)
joinAnn (JustAssign xs) (JustAssign ys) = return $ JustAssign (xs ++ ys)
joinAnn (JustAssign []) s@(CmdAssign _ _) = return s
joinAnn (Annotation l p r) r' = Annotation l p <$> joinAnn r r'
joinAnn l' (Annotation l p r) = joinAnn l' l >>= \l'' -> return $ Annotation l'' p r
joinAnn _ _ = Nothing

--------------------------------------------------------------------------------
--  Generating verification conditions
--------------------------------------------------------------------------------

-- | A function that generates verification conditions from something of type
-- 'a', given a precondition and a postcondition.
type GenVCs f expr var a = Prop expr var -> Prop expr var -> a -> f [Prop expr var]


-- | Generates verification conditions for a skip statement.
skipVCs
  :: (Substitutive expr, Applicative f)
  => GenVCs f expr (Var l) ()
skipVCs precond postcond () = pure [precond `pImpl` postcond]


-- | Generates verification conditions for an assignment.
assignVCs
  :: (Substitutive expr, Applicative f, Location l)
  => GenVCs f expr (Var l) (Assignment expr (Var l))
assignVCs precond postcond assignment =
  let postcond' = subAssignment assignment postcond
  in pure [precond `pImpl` postcond']


-- | Generates verification conditions for a sequence of commands.
sequenceVCs
  :: (Substitutive expr, Applicative f, Location l)
  => GenVCs f expr (Var l) cmd
  -> GenVCs f expr (Var l) (AnnSeq expr (Var l) cmd)
sequenceVCs cmdVCs precond postcond annSeq =
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
      in cmdVCs precond postcond' cmd

    -- To verify @{P} C_1 ; {R} C_2 {Q}@, verify @{P} C_1 {R}@ and @{R} C_2 {Q}@.
    Annotation l midcond r ->
      (++) <$> sequenceVCs cmdVCs precond midcond l
           <*> sequenceVCs cmdVCs midcond postcond r


-- | Generates verification conditions for a two-branch if command.
ifVCs
  :: (Substitutive expr, Applicative f)
  => GenVCs f expr (Var l) cmd
  -> (cond -> Prop expr (Var l))
  -> GenVCs f expr (Var l) (cond, cmd, cmd)
ifVCs cmdVCs condToProp precond postcond (cond, cmd1, cmd2) =
  let condProp = condToProp cond
  in (++) <$> cmdVCs (precond `pAnd` condProp) postcond cmd1
          <*> cmdVCs (precond `pAnd` pNot condProp) postcond cmd2


-- | Generates verification conditions for a while loop.
whileVCs
  :: (Substitutive expr, Applicative f)
  => GenVCs f expr (Var l) cmd
  -> (cond -> Prop expr (Var l))
  -> Prop expr (Var l) -- ^ Loop invariant
  -> GenVCs f expr (Var l) (cond, cmd)
whileVCs cmdVCs condToProp invariant precond postcond (cond, body) =
  let condProp = condToProp cond
      invariantMaintained = cmdVCs (invariant `pAnd` condProp) invariant body
      invariantWorks = [precond `pImpl` invariant, (invariant `pAnd` pNot condProp) `pImpl` postcond]
  in (invariantWorks ++) <$> invariantMaintained

