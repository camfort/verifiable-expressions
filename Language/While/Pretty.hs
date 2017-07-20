{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE LambdaCase #-}

module Language.While.Pretty where

import Data.List (intercalate)

import Language.While.Syntax
import Language.While.Hoare


class Pretty a where
  pretty :: a -> String


instance Pretty l => Pretty (Expr l) where
  pretty = \case
    EAdd e1 e2 -> pretty e1 ++ " + " ++ pretty e2
    EMul e1 e2 -> "(" ++ pretty e1 ++ ") * (" ++ pretty e2 ++ ")"
    ESub e1 e2 -> "(" ++ pretty e1 ++ ") - (" ++ pretty e2 ++ ")"
    EVar loc -> pretty loc
    ELit x -> show x


instance Pretty l => Pretty (Bexpr l) where
  pretty = \case
    BLess e1 e2 -> pretty e1 ++ " < " ++ pretty e2
    BLessEq e1 e2 -> pretty e1 ++ " <= " ++ pretty e2
    BEq e1 e2 -> pretty e1 ++ " = " ++ pretty e2
    BAnd b1 b2 -> "(" ++ pretty b1 ++ ") && (" ++ pretty b2 ++ ")"
    BOr b1 b2 -> "(" ++ pretty b1 ++ ") || (" ++ pretty b2 ++ ")"
    BNot bexpr -> "¬ (" ++ pretty bexpr ++ ")"


instance Pretty l => Pretty (Prop l) where
  pretty = \case
    PBexpr bexpr -> pretty bexpr
    PAnd p1 p2 -> "(" ++ pretty p1 ++ ") && (" ++ pretty p2 ++ ")"
    POr p1 p2 -> "(" ++ pretty p1 ++ ") || (" ++ pretty p2 ++ ")"
    PImplies p1 p2 -> "(" ++ pretty p1 ++ ") => (" ++ pretty p2 ++ ")"
    PNot prop -> "¬ (" ++ pretty prop ++ ")"
    PTrue -> "T"
    PFalse -> "F"


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
