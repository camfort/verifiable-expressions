{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.While.Pretty where

import           Data.List             (intercalate)

import           Language.Expression hiding (Expr)
import           Language.While.Prop   as P
import           Language.While.Syntax as S


class Pretty a where
  pretty :: a -> String

instance Pretty a => Pretty (ExprOp a) where
  pretty =
    let combine = \case
          OAdd a b -> a ++ " + " ++ b
          OMul a b -> "(" ++ a ++ ") * (" ++ b ++ ")"
          OSub a b -> "(" ++ a ++ ") - (" ++ b ++ ")"
          S.OLit x -> show x
    in combine . fmap pretty

instance Pretty a => Pretty (ArithOp a) where
  pretty =
    let combine = \case
          OLess a b -> a ++ " < " ++ b
          OLessEq a b -> a ++ " <= " ++ b
          OEq a b -> a ++ " = " ++ b
    in combine . fmap pretty

instance Pretty a => Pretty (BoolOp a) where
  pretty =
    let combine = \case
          S.OAnd a b -> "(" ++ a ++ ") & (" ++ b ++ ")"
          S.OOr a b -> "(" ++ a ++ ") | (" ++ b ++ ")"
          S.ONot a -> "! (" ++ a ++ ")"
    in combine . fmap pretty

instance Pretty a => Pretty (PropOp a) where
  pretty =
    let combine = \case
          P.OAnd a b -> "(" ++ a ++ ") & (" ++ b ++ ")"
          P.OOr a b -> "(" ++ a ++ ") | (" ++ b ++ ")"
          P.OImpl a b -> "(" ++ a ++ ") -> (" ++ b ++ ")"
          P.OEquiv a b -> "(" ++ a ++ ") <-> (" ++ b ++ ")"
          P.ONot a -> "! (" ++ a ++ ")"
          P.OLit True -> "T"
          P.OLit False -> "F"
    in combine . fmap pretty

instance Pretty l => Pretty (Expr l) where
  pretty = \case
    SOp op -> pretty op
    SVar loc -> pretty loc

instance Pretty l => Pretty (Bexpr l) where
  pretty = \case
    BArithOp op -> pretty op
    BBoolOp op -> pretty op

instance Pretty a => Pretty (Prop a) where
  pretty = \case
    SVar a -> pretty a
    SOp op -> pretty op

instance Pretty l => Pretty (Maybe l) where
  pretty = \case
    Nothing -> "<nothing>"
    Just l -> pretty l

instance {-# OVERLAPPABLE #-} Pretty l => Pretty [l] where
  pretty xs =
    let pretties = map pretty xs
    in "[ " ++
       intercalate "\n, " pretties ++
       "\n]"

instance {-# OVERLAPPING #-} Pretty String where
  pretty = id

putPretty :: Pretty a => a -> IO ()
putPretty = putStrLn . pretty
