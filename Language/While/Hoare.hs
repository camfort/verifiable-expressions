{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE LambdaCase         #-}

module Language.While.Hoare where
  -- ( WhileProp
  -- , evalWhileProp
  -- , substWhileProp
  -- , PropAnn(..)
  -- , AnnCommand
  -- , generateVcs
  -- ) where

import           Language.While.Prop                  as P
import           Language.While.Syntax                as S

import qualified Language.Verification                as V
import qualified Language.Verification.Conditions     as V
import qualified Language.Expression     as V
import qualified Language.Expression.Operators     as V
import           Language.Expression.DSL hiding (Expr, Prop)
import qualified Language.Expression.DSL as VD

--------------------------------------------------------------------------------
--  Translating expressions in WHILE
--------------------------------------------------------------------------------

type VExpr l a = VD.Expr' V.StandardOps (V.Var l) a

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

translateExprOp :: ExprOp (VExpr l Integer) -> VExpr l Integer
translateExprOp = \case
  S.OAdd x y -> x .+ y
  S.OMul x y -> x .* y
  S.OSub x y -> x .- y

translateExpr :: Expr l -> VExpr l Integer
translateExpr = \case
  EOp op -> translateExprOp $ fmap translateExpr op
  EVar x -> var (V.Var x)
  ELit x -> lit x

translateBexpr :: Bexpr l -> VExpr l Bool
translateBexpr = \case
  BArithOp op -> translateArithOp $ fmap translateExpr op
  BBoolOp op -> translateBoolOp $ fmap translateBexpr op
  -- evalBexprGeneral translateArithOp translateBoolOp _

--------------------------------------------------------------------------------
--  Translating propositions over WHILE
--------------------------------------------------------------------------------

type VProp l a = VD.Prop V.StandardOps (V.Var l) a

translatePropOp :: PropOp (VProp l Bool) -> VProp l Bool
translatePropOp = \case
  P.OAnd x y -> x *&& y
  P.OOr x y -> x *|| y
  P.OImpl x y -> x *-> y
  P.OEquiv x y -> x *<-> y
  P.ONot x -> pnot x

translateProp :: Prop (Bexpr l) -> VProp l Bool
translateProp = \case
  POp op -> translatePropOp $ fmap translateProp op
  PLit x -> plit x
  PEmbed x -> expr (translateBexpr x)

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


generateVCs' :: (V.Location l) => V.GenVCs Maybe (VD.Expr' V.StandardOps) (V.Var l) (AnnCommand l a)
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
