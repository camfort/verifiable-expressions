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

type VProp l = Prop (Expr WhileOp (WhileVar l))

instance (Pretty l, Pretty a) => Pretty (PropAnn l a) where
  prettysPrec _ (PropAnn prop ann) = prettysPrec 10 prop . showString " , " . prettysPrec 10 ann

translateExpr :: WhileExpr l a -> Expr WhileOp (WhileVar l) a
translateExpr = hmapOp (\(WhileVar s) -> WhileVar s)

translateProp :: WhileProp l a -> VProp l a
translateProp = hmapOp translateExpr

type MonadGen l = WriterT [VProp l Bool] Maybe

--------------------------------------------------------------------------------
--  Exposed Functions
--------------------------------------------------------------------------------

-- | Generate verification conditions to prove that the given Hoare partial
-- correctness triple holds.
generateVCs
  :: (VerifiableVar (WhileVar l))
  => WhileProp l Bool -> WhileProp l Bool -> AnnCommand l a
  -> Maybe [VProp l Bool]
generateVCs precond postcond cmd =
  execWriterT $ generateVCs' (translateProp precond, translateProp postcond, cmd)


generateVCs'
  :: (VerifiableVar (WhileVar l))
  => Triplet (Expr WhileOp) (WhileVar l) (AnnCommand l a) -> MonadGen l ()
generateVCs' (precond, postcond, cmd) = case cmd of
  CAnn (PropAnn prop _) command ->
    generateVCs' ((translateProp prop *&& precond), postcond, command)

  c@(CSeq _ _) -> do
    s <- lift (splitSeq c)
    void $ sequenceVCs generateVCs' (precond, postcond, s)

  CSkip -> skipVCs (precond, postcond, ())

  CAssign loc e ->
    assignVCs (precond, postcond, (Assignment (WhileVar loc) (translateExpr e)))

  CIf cond c1 c2 ->
    void $ ifVCs generateVCs' (expr . translateExpr) (precond, postcond, (cond, c1, c2))

  CWhile cond (CAnn (PropAnn invariant _) body) ->
    whileVCs generateVCs'
      (expr . translateExpr)
      (translateProp invariant)
      (precond, postcond, (cond, body))

  -- If this falls through, the command is not sufficiently annotated
  _ -> mzero

--------------------------------------------------------------------------------
--  Internal
--------------------------------------------------------------------------------

-- | Split the command into all the top-level sequenced commands, interspersed
-- with annotations. Returns 'Nothing' if the command's sequences are not
-- sufficiently annotated.
splitSeq :: AnnCommand l a -> Maybe (AnnSeq (Expr WhileOp) (WhileVar l) (AnnCommand l a))
splitSeq = \case
  CSeq c1 (CAnn (PropAnn midcond _) c2) ->
    do a1 <- splitSeq c1
       a2 <- splitSeq c2
       return $ Annotation a1 (translateProp midcond) a2
  CSeq c1 (CAssign loc e) ->
    do a1 <- splitSeq c1
       a1 `joinAnnSeq` JustAssign [Assignment (WhileVar loc) (translateExpr e)]
  CSeq c1 c2 ->
    do a1 <- splitSeq c1
       a2 <- splitSeq c2
       a1 `joinAnnSeq` a2
  CAssign loc e -> return $ JustAssign [Assignment (WhileVar loc) (translateExpr e)]
  c -> return $ CmdAssign c []
