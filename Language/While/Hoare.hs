{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE TypeFamilies       #-}

module Language.While.Hoare where

import Control.Monad.Writer

import           Language.While.Syntax

import           Language.Expression.Prop
import           Language.Expression.Pretty
import           Language.Verification
import           Language.Verification.Conditions

type WhileProp l = Prop (WhileExpr l)

data PropAnn l a = PropAnn (WhileProp l Bool) a

type AnnCommand l a = Command l (PropAnn l a)

instance (Pretty l, Pretty a) => Pretty (PropAnn l a) where
  prettysPrec _ (PropAnn prop ann) = prettysPrec 10 prop . showString " , " . prettysPrec 10 ann

type MonadGen l = WriterT [WhileProp l Bool] Maybe

--------------------------------------------------------------------------------
--  Exposed Functions
--------------------------------------------------------------------------------

-- | Generate verification conditions to prove that the given Hoare partial
-- correctness triple holds.
generateVCs
  :: (VerifiableVar (WhileVar l))
  => WhileProp l Bool -> WhileProp l Bool -> AnnCommand l a
  -> Maybe [WhileProp l Bool]
generateVCs precond postcond cmd =
  execWriterT $ generateVCs' (precond, postcond, cmd)


generateVCs'
  :: (VerifiableVar (WhileVar l))
  => Triplet (HFree WhileOp) (WhileVar l) (AnnCommand l a) -> MonadGen l ()
generateVCs' (precond, postcond, cmd) = case cmd of
  CAnn (PropAnn prop _) command ->
    generateVCs' ((prop *&& precond), postcond, command)

  c@(CSeq _ _) -> do
    s <- lift (splitSeq c)
    void $ sequenceVCs generateVCs' (precond, postcond, s)

  CSkip -> skipVCs (precond, postcond, ())

  CAssign loc e ->
    assignVCs (precond, postcond, (Assignment (WhileVar loc) e))

  CIf cond c1 c2 ->
    void $ ifVCs generateVCs' expr (precond, postcond, (cond, c1, c2))

  CWhile cond (CAnn (PropAnn invariant _) body) ->
    whileVCs generateVCs'
      expr
      invariant
      (precond, postcond, (cond, body))

  -- If this falls through, the command is not sufficiently annotated
  _ -> mzero

--------------------------------------------------------------------------------
--  Internal
--------------------------------------------------------------------------------

-- | Split the command into all the top-level sequenced commands, interspersed
-- with annotations. Returns 'Nothing' if the command's sequences are not
-- sufficiently annotated.
splitSeq :: AnnCommand l a -> Maybe (AnnSeq (HFree WhileOp) (WhileVar l) (AnnCommand l a))
splitSeq = \case
  CSeq c1 (CAnn (PropAnn midcond _) c2) ->
    do a1 <- splitSeq c1
       a2 <- splitSeq c2
       return $ Annotation a1 midcond a2
  CSeq c1 (CAssign loc e) ->
    do a1 <- splitSeq c1
       a1 `joinAnnSeq` JustAssign [Assignment (WhileVar loc) e]
  CSeq c1 c2 ->
    do a1 <- splitSeq c1
       a2 <- splitSeq c2
       a1 `joinAnnSeq` a2
  CAssign loc e -> return $ JustAssign [Assignment (WhileVar loc) e]
  c -> return $ CmdAssign c []
