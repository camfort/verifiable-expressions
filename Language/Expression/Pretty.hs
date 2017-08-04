{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NoMonomorphismRestriction        #-}

{-|

Pretty printing for expressions.

-}
module Language.Expression.Pretty
  ( putPretty
  , Pretty(..)
  , prettys
  , Pretty1(..)
  , prettys1
  , Pretty2(..)
  , prettys2
  ) where

-- import Prelude hiding (showParen)

import           Data.Functor.Const
import           Data.List                                  (intercalate)

import           Language.Verification
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

prettys :: Pretty a => a -> ShowS
prettys = prettysPrec 0

prettys1 :: Pretty1 t => t a -> ShowS
prettys1 = prettys1Prec 0

prettys2 :: (Pretty2 op, Pretty1 t) => op t a -> ShowS
prettys2 = prettys2Prec 0

class Pretty a where
  {-# MINIMAL pretty | prettysPrec #-}

  pretty :: a -> String
  prettysPrec :: Int -> a -> ShowS

  pretty x = prettys x ""
  prettysPrec _ x s = pretty x ++ s

class Pretty1 t where
  {-# MINIMAL pretty1 | prettys1Prec #-}

  pretty1 :: t a -> String
  pretty1 x = prettys1 x ""

  prettys1Prec :: Int -> t a -> ShowS
  prettys1Prec _ x s = pretty1 x ++ s

class Pretty2 op where
  {-# MINIMAL pretty2 | prettys2Prec #-}

  pretty2 :: (Pretty1 t) => op t a -> String
  pretty2 x = prettys2 x ""

  prettys2Prec :: (Pretty1 t) => Int -> op t a -> ShowS
  prettys2Prec _ x s = pretty2 x ++ s

--------------------------------------------------------------------------------
--  Operator instances
--------------------------------------------------------------------------------

instance Pretty2 BoolOp where
  prettys2Prec p = \case
    OpNot x -> showParen (p > 8) $ showString "! " . prettys1Prec 9 x
    OpAnd x y ->
      showParen (p > 3) $ prettys1Prec 4 x . showString " && " . prettys1Prec 4 y

    OpOr x y ->
      showParen (p > 2) $ prettys1Prec 3 x . showString " || " . prettys1Prec 3 y

instance Pretty2 LogicOp where
  prettys2Prec p = \case
    LogLit True -> \r -> "T" ++ r
    LogLit False -> \r -> "F" ++ r
    LogNot x -> showParen (p > 8) $ showString "¬ " . prettys1Prec 9 x
    LogAnd x y ->
      showParen (p > 3) $ prettys1Prec 4 x . showString " ∧ " . prettys1Prec 4 y
    LogOr  x y ->
      showParen (p > 2) $ prettys1Prec 3 x . showString " ∨ " . prettys1Prec 3 y
    LogImpl  x y ->
      showParen (p > 1) $ prettys1Prec 2 x . showString " -> " . prettys1Prec 2 y
    LogEquiv  x y ->
      showParen (p > 0) $ prettys1Prec 1 x . showString " <-> " . prettys1Prec 1 y

instance Pretty2 NumOp where
  prettys2Prec p = \case
    OpAdd x y ->
      showParen (p > 5) $ prettys1Prec 6 x . showString " + " . prettys1Prec 6 y
    OpSub x y ->
      showParen (p > 5) $ prettys1Prec 6 x . showString " - " . prettys1Prec 6 y
    OpMul x y ->
      showParen (p > 6) $ prettys1Prec 7 x . showString " * " . prettys1Prec 7 y

instance Pretty2 LitOp where
  prettys2Prec p = \case
    OpLit x -> showString $ prettyValuePrec p x

instance Pretty2 EqOp where
  prettys2Prec p = \case
    OpEq x y ->
      showParen (p > 4) $ prettys1Prec 5 x . showString " = " . prettys1Prec 5 y

instance Pretty2 OrdOp where
  prettys2Prec p = \case
    OpLT x y ->
      showParen (p > 4) $ prettys1Prec 5 x . showString " < " . prettys1Prec 5 y
    OpLE x y ->
      showParen (p > 4) $ prettys1Prec 5 x . showString " <= " . prettys1Prec 5 y
    OpGT x y ->
      showParen (p > 4) $ prettys1Prec 5 x . showString " > " . prettys1Prec 5 y
    OpGE x y ->
      showParen (p > 4) $ prettys1Prec 5 x . showString " >= " . prettys1Prec 5 y

instance Pretty2 CoerceOp where
  prettys2Prec p = \case
    OpCoerce x -> prettys1Prec p x

--------------------------------------------------------------------------------
--  Combinatory instances
--------------------------------------------------------------------------------

instance {-# OVERLAPPABLE #-} (Pretty1 t) => Pretty (t a) where
  prettysPrec = prettys1Prec

instance {-# OVERLAPPABLE #-} (Pretty2 f, Pretty1 t) => Pretty1 (f t) where
  prettys1Prec = prettys2Prec

instance Pretty1 (Const String) where
  pretty1 (Const x) = x

instance (Pretty2 op, Operator op) => Pretty2 (Expr op) where
  prettys2Prec p = \case
    EVar x -> prettys1Prec p x
    EOp op -> prettys2Prec p op

instance (Pretty2 (OpChoice ops), Operator (OpChoice ops)) =>
  Pretty2 (Expr' ops) where

  prettys2Prec p = prettys2Prec p . getExpr'

instance (Pretty2 (OpChoice '[])) where
  pretty2 x = case x of
    -- absurd

instance (Pretty2 op, Pretty2 (OpChoice ops)) => Pretty2 (OpChoice (op : ops)) where
  prettys2Prec p = \case
    Op0 x -> prettys2Prec p x
    OpS x -> prettys2Prec p x

instance {-# OVERLAPPING #-} Pretty String where
  pretty = id

instance {-# OVERLAPPING #-} Pretty a => Pretty [a] where
  pretty xs =
    "[ " ++
    -- (intercalate "\n, " . map (\x -> prettysPrec 11 x "")) xs ++
    (intercalate "\n, " . map pretty) xs ++
    "\n]"

instance {-# OVERLAPPING #-} Pretty a => Pretty (Maybe a) where
  prettysPrec p (Just x) = prettysPrec p x
  prettysPrec _ Nothing = \r -> "<nothing>" ++ r

instance Pretty1 (Var String) where
  pretty1 (Var x) = x

instance Pretty () where
  pretty = show
