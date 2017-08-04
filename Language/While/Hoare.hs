{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE TypeFamilies       #-}

module Language.While.Hoare where
  -- ( WhileProp
  -- , evalWhileProp
  -- , substWhileProp
  -- , PropAnn(..)
  -- , AnnCommand
  -- , generateVcs
  -- ) where

import           Control.Lens                     hiding (op)

import           Data.Typeable                    ((:~:) (..))

import           Language.While.Prop              as P
import           Language.While.Syntax            as S

import           Language.Expression.DSL          hiding (Expr, Prop)
import qualified Language.Verification            as V
import qualified Language.Verification.Conditions as V hiding (Prop)

--------------------------------------------------------------------------------
--  Translating expressions in WHILE
--------------------------------------------------------------------------------

type VExpr l a = V.Expr' V.StandardOps (V.Var l) a

translateArithOp :: ArithOp (VExpr l Integer) -> VExpr l Bool
translateArithOp = \case
  OLess x y -> x .< y
  OLessEq x y -> x .<= y
  OEq x y -> x .== y

translateBoolOp :: BoolOp (VExpr l Bool) -> VExpr l Bool
translateBoolOp = \case
  S.OAnd x y -> x .&& y
  S.OOr x y -> x .|| y
  S.ONot x -> enot x

translateExprOp :: ExprOp (t Integer) -> V.OpChoice V.StandardOps t Integer
translateExprOp = \case
  S.OAdd x y -> V.OpAdd x y ^. re V.chooseOp
  S.OMul x y -> V.OpMul x y ^. re V.chooseOp
  S.OSub x y -> V.OpSub x y ^. re V.chooseOp
  S.OLit x -> V.OpLit x ^. re V.chooseOp

translateExpr :: Expr l -> VExpr l Integer
translateExpr =
  V.Expr' .
  V.mapOperators (\(V.RestrictOp Refl x) -> translateExprOp . V.unliftOp $ x) .
  review V._SimpleExpr' .
  fmap V.Var

translateBexpr :: Bexpr l -> VExpr l Bool
translateBexpr = \case
  BArithOp op -> translateArithOp $ fmap translateExpr op
  BBoolOp op -> translateBoolOp $ fmap translateBexpr op
  -- evalBexprGeneral translateArithOp translateBoolOp _

--------------------------------------------------------------------------------
--  Translating propositions over WHILE
--------------------------------------------------------------------------------

type VProp l a = V.Prop V.StandardOps (V.Var l) a


translatePropOp :: PropOp (t Bool) -> V.LogicOp t Bool
translatePropOp = \case
  P.OAnd x y -> V.LogAnd x y
  P.OOr x y -> V.LogOr x y
  P.OImpl x y -> V.LogImpl x y
  P.OEquiv x y -> V.LogEquiv x y
  P.ONot x -> V.LogNot x
  P.OLit x -> V.LogLit x


translateProp :: Prop (Bexpr l) -> V.PropOver (V.Expr' V.StandardOps (V.Var l)) Bool
translateProp =
  V.mapOperators (\(V.RestrictOp Refl x) -> translatePropOp . V.unliftOp $ x) .
  (^. re V._SimpleExpr') .
  fmap translateBexpr

--------------------------------------------------------------------------------
--  Exposed Data Types
--------------------------------------------------------------------------------

type WhileProp l = Prop (Bexpr l)

data PropAnn l a = PropAnn (WhileProp l) a
  deriving (Show, Functor, Foldable, Traversable)

type AnnCommand l a = Command l (PropAnn l a)

--------------------------------------------------------------------------------
--  Exposed Functions
--------------------------------------------------------------------------------

-- | Generate verification conditions to prove that the given Hoare partial
-- correctness triple holds.
generateVCs :: (V.Location l) => WhileProp l -> WhileProp l -> AnnCommand l a -> Maybe [VProp l Bool]
generateVCs precond postcond = generateVCs' (translateProp precond) (translateProp postcond)


generateVCs' :: (V.Location l) => V.GenVCs Maybe (V.Expr' V.StandardOps) (V.Var l) (AnnCommand l a)
generateVCs' precond postcond = \case
  CAnn (PropAnn prop _) command ->
    generateVCs' (translateProp prop *&& precond) postcond command

  c@(CSeq _ _) ->
    splitSeq c >>= V.sequenceVCs generateVCs' precond postcond

  CSkip -> V.skipVCs precond postcond ()

  CAssign loc e ->
    V.assignVCs precond postcond (V.Assignment (V.Var loc) (translateExpr e))

  CIf cond c1 c2 ->
    V.ifVCs generateVCs' (expr . translateBexpr) precond postcond (cond, c1, c2)

  CWhile cond (CAnn (PropAnn invariant _) body) ->
    V.whileVCs generateVCs'
      (expr . translateBexpr)
      (translateProp invariant)
      precond postcond (cond, body)

  -- If this falls through, the command is not sufficiently annotated
  _ -> Nothing

--------------------------------------------------------------------------------
--  Internal
--------------------------------------------------------------------------------

-- | Split the command into all the top-level sequenced commands, interspersed
-- with annotations. Returns 'Nothing' if the command's sequences are not
-- sufficiently annotated.
splitSeq :: AnnCommand l a -> Maybe (V.AnnSeq (V.Expr' V.StandardOps) (V.Var l) (AnnCommand l a))
splitSeq = \case
  CSeq c1 (CAnn (PropAnn midcond _) c2) ->
    do a1 <- splitSeq c1
       a2 <- splitSeq c2
       return $ V.Annotation a1 (translateProp midcond) a2
  CSeq c1 (CAssign loc e) ->
    do a1 <- splitSeq c1
       a1 `V.joinAnn` V.JustAssign [V.Assignment (V.Var loc) (translateExpr e)]
  CSeq c1 c2 ->
    do a1 <- splitSeq c1
       a2 <- splitSeq c2
       a1 `V.joinAnn` a2
  CAssign loc e -> return $ V.JustAssign [V.Assignment (V.Var loc) (translateExpr e)]
  c -> return $ V.CmdAssign c []
