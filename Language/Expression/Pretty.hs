{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

{-|

Pretty printing for expressions.

-}
module Language.Expression.Pretty
  (
  -- * Classes
    Pretty(..)
  , prettys
  , Pretty1(..)
  , prettys1
  , Pretty2(..)
  , prettys2
  -- * Combinators
  , putPretty
  , prettys1PrecBinop
  , prettys1PrecUnop
  ) where

import           Data.Functor.Const
import           Data.List           (intersperse)
import           Data.Monoid         (Endo (..))

import           Language.Expression

--------------------------------------------------------------------------------
--  Convenience
--------------------------------------------------------------------------------

putPretty :: Pretty a => a -> IO ()
putPretty = putStrLn . pretty

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

prettys1PrecUnop :: Pretty1 t => Int -> String -> Int -> t a -> ShowS
prettys1PrecUnop opPrec opStr p x =
  showParen (p > opPrec) $ showString opStr . prettys1Prec (opPrec + 1) x

prettys1PrecBinop :: (Pretty1 f, Pretty1 g) => Int -> String -> Int -> f a -> g b -> ShowS
prettys1PrecBinop opPrec opStr p x y =
  showParen (p > opPrec) $ prettys1Prec (opPrec + 1) x . showString opStr . prettys1Prec (opPrec + 1) y

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

class Pretty1 (t :: k -> *) where
  {-# MINIMAL pretty1 | prettys1Prec #-}

  pretty1 :: t a -> String
  pretty1 x = prettys1 x ""

  prettys1Prec :: Int -> t a -> ShowS
  prettys1Prec _ x s = pretty1 x ++ s

class Pretty2 (op :: (k -> *) -> k -> *) where
  {-# MINIMAL pretty2 | prettys2Prec #-}

  pretty2 :: (Pretty1 t) => op t a -> String
  pretty2 x = prettys2 x ""

  prettys2Prec :: (Pretty1 t) => Int -> op t a -> ShowS
  prettys2Prec _ x s = pretty2 x ++ s

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
    OpThis x -> prettys2Prec p x
    OpThat x -> prettys2Prec p x

instance {-# OVERLAPPING #-} Pretty String where
  pretty = id

instance {-# OVERLAPPING #-} Pretty a => Pretty [a] where
  prettysPrec _ xs = (appEndo . mconcat . map Endo) (
    showString "[ " : (intersperse (showString "\n, ") . map prettys) xs) .
    showString "\n]"

instance {-# OVERLAPPING #-} Pretty a => Pretty (Maybe a) where
  prettysPrec p (Just x) = prettysPrec p x
  prettysPrec _ Nothing = \r -> "<nothing>" ++ r

instance Pretty () where
  pretty = show
