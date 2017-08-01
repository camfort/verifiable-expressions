{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}

{-|

Pretty printing for expressions.

-}
module Language.Expression.Pretty
  ( putPretty
  , Pretty(..)
  , Pretty1(..)
  , Pretty2(..)
  ) where

import           Data.Functor.Const
import           Data.List                                  (intercalate)

import           Language.Verification
import           Language.Expression
import           Language.Expression.Operators
import           Language.Expression.Classes           (prettyValuePrec)

--------------------------------------------------------------------------------
--  Convenience
--------------------------------------------------------------------------------

putPretty :: Pretty a => a -> IO ()
putPretty = putStrLn . pretty

--------------------------------------------------------------------------------
--  Pretty typeclasses
--------------------------------------------------------------------------------

class Pretty a where
  pretty :: a -> String
  pretty = prettyPrec 0

  prettyPrec :: Int -> a -> String
  prettyPrec _ = pretty

class Pretty1 t where
  pretty1 :: t a -> String
  pretty1 = pretty1Prec 0

  pretty1Prec :: Int -> t a -> String
  pretty1Prec _ = pretty1

class Pretty2 f where
  pretty2 :: (Pretty1 t) => f t a -> String
  pretty2 = pretty2Prec 0

  pretty2Prec :: (Pretty1 t) => Int -> f t a -> String
  pretty2Prec _ = pretty2

--------------------------------------------------------------------------------
--  Operator instances
--------------------------------------------------------------------------------

paren :: Int -> Int -> String -> String
paren x y s
  | x <= y = "(" ++ s ++ ")"
  | otherwise = s

instance Pretty2 BoolOp where
  pretty2Prec p = \case
    OpNot x -> paren p 8 $ "¬ " ++ pretty1Prec 8 x
    OpAnd x y -> paren p 3 $ pretty1Prec 3 x ++ " ∧ " ++ pretty1Prec 3 y
    OpOr  x y -> paren p 2 $ pretty1Prec 2 x ++ " ∨ " ++ pretty1Prec 2 y
    OpImpl  x y -> paren p 1 $ pretty1Prec 1 x ++ " -> " ++ pretty1Prec 1 y
    OpEquiv  x y -> paren p 0 $ pretty1Prec 0 x ++ " <-> " ++ pretty1Prec 0 y

instance Pretty2 NumOp where
  pretty2Prec p = \case
    OpAdd x y -> paren p 5 $ pretty1Prec 5 x ++ " + " ++ pretty1Prec 5 y
    OpSub x y -> paren p 5 $ pretty1Prec 5 x ++ " - " ++ pretty1Prec 5 y
    OpMul x y -> paren p 6 $ pretty1Prec 6 x ++ " * " ++ pretty1Prec 6 y

instance Pretty2 LitOp where
  pretty2Prec p = \case
    OpLit x -> prettyValuePrec p x

instance Pretty2 EqOp where
  pretty2Prec p = \case
    OpEq x y -> paren p 4 $ pretty1Prec 4 x ++ " = " ++ pretty1Prec 4 y

instance Pretty2 OrdOp where
  pretty2Prec p = \case
    OpLT x y -> paren p 4 $ pretty1Prec 4 x ++ " < " ++ pretty1Prec 4 y
    OpLE x y -> paren p 4 $ pretty1Prec 4 x ++ " <= " ++ pretty1Prec 4 y
    OpGT x y -> paren p 4 $ pretty1Prec 4 x ++ " > " ++ pretty1Prec 4 y
    OpGE x y -> paren p 4 $ pretty1Prec 4 x ++ " >+ " ++ pretty1Prec 4 y

--------------------------------------------------------------------------------
--  Combinatory instances
--------------------------------------------------------------------------------

instance {-# OVERLAPPABLE #-} (Pretty1 t) => Pretty (t a) where
  pretty = pretty1

instance {-# OVERLAPPABLE #-} (Pretty2 f, Pretty1 t) => Pretty1 (f t) where
  pretty1 = pretty2

instance Pretty1 (Const String) where
  pretty1 (Const x) = x

instance (Pretty2 op, Operator op) => Pretty2 (Expr op) where
  pretty2Prec p = \case
    EVar x -> pretty1Prec p x
    EOp op -> pretty2Prec p $ hmapOp (Const . pretty2Prec p) op

instance (Pretty2 (OpChoice ops), Operator (OpChoice ops)) => Pretty2 (Expr' ops) where
  pretty2Prec p = pretty2Prec p . getExpr'

instance (Pretty2 (OpChoice '[])) where
  pretty2 x = case x of
    -- absurd

instance (Pretty2 op, Pretty2 (OpChoice ops)) => Pretty2 (OpChoice (op : ops)) where
  pretty2Prec p = \case
    Op0 x -> pretty2Prec p x
    OpS x -> pretty2Prec p x

instance {-# OVERLAPPING #-} Pretty a => Pretty [a] where
  pretty xs =
    "[ " ++
    (intercalate "\n, " . map pretty) xs ++
    "\n]"

instance {-# OVERLAPPING #-} Pretty a => Pretty (Maybe a) where
  pretty (Just x) = pretty x
  pretty Nothing = "<nothing>"

instance Pretty1 (Var String) where
  pretty1 (Var x) = x
