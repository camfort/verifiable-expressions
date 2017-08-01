{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Language.Expression.Dynamic where

import Data.Typeable

import Language.Expression
import Language.Verification.SymClasses2

data BinOp
  = DopAdd
  | DopSub
  | DopMul
  | DopLT
  | DopLE
  | DopGT
  | DopGE
  | DopEq
  | DopNeq
  | DopAnd
  | DopOr
  | DopImpl
  | DopEquiv
  deriving (Show)

data DynLit
  = LitInteger Integer
  | LitBool Bool
  deriving (Show)

data DynOp t a where
  DBinOp :: BinOp -> t a -> t a -> DynOp t a
  DopNot :: t a -> DynOp t a
  DopLit :: DynLit -> DynOp t a
  deriving (Show, Typeable)


instance Operator DynOp where
  htraverseOp f = \case
    DBinOp op x y -> DBinOp op <$> f x <*> f y
    DopNot x -> DopNot <$> f x
    DopLit x -> pure $ DopLit x

  evalOp = error "Can't directly evaluate a 'DynOp'"


type DynExpr v a = Expr DynOp v a

binop ::
  BinOp -> Expr DynOp v a -> Expr DynOp v a -> Expr DynOp v a
binop op x y = EOp (DBinOp op x y)

instance SymValue (DynExpr v a) where
  prettyValue _ = "<dynamic value>"

instance SymBool (DynExpr v a) where
  symFromBool = EOp . DopLit . LitBool

  symAnd = binop DopAnd
  symOr = binop DopOr
  symImpl = binop DopImpl
  symEquiv = binop DopEquiv

  symNot = EOp . DopNot

instance SymEq (DynExpr v a) (DynExpr v a) where
  symEq = binop DopEq
  symNeq = binop DopNeq

instance SymOrd (DynExpr v a) (DynExpr v a) where
  symLt = binop DopLT
  symLe = binop DopLE
  symGt = binop DopGT
  symGe = binop DopGE

instance SymNum (DynExpr v a) where
  symAdd = binop DopAdd
  symSub = binop DopSub
  symMul = binop DopMul


newtype Sym a = Sym { getSym :: forall v b. DynExpr v b }
  deriving (Functor, Foldable, Traversable, Typeable)

joinSym :: Sym (Sym a) -> Sym a
joinSym (Sym x) = Sym x

instance SymValue (Sym a) where
  prettyValue = prettyValue . getSym

instance SymBool (Sym a) where
  symFromBool b = Sym (symFromBool b)

  symAnd (Sym x) (Sym y) = Sym (symAnd x y)
  symOr (Sym x) (Sym y) = Sym (symOr x y)
  symImpl (Sym x) (Sym y) = Sym (symImpl x y)
  symEquiv (Sym x) (Sym y) = Sym (symEquiv x y)

  symNot (Sym x) = Sym (symNot x)

instance SymEq (Sym b) (Sym a) where
