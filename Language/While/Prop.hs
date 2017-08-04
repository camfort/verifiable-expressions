{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE PatternSynonyms    #-}

module Language.While.Prop where

import           Data.Data

import           Language.Expression

data PropOp a
  = OAnd a a
  | OOr a a
  | OImpl a a
  | OEquiv a a
  | ONot a
  | OLit Bool
  deriving (Show, Eq, Ord, Data, Typeable, Functor, Foldable, Traversable)


type Prop = SimpleExpr PropOp


evalOpBool :: PropOp Bool -> Bool
evalOpBool =
  let impl a b = not a || b
  in \case
    OAnd a b -> a && b
    OOr a b -> a || b
    OImpl a b -> a `impl` b
    OEquiv a b -> (a `impl` b) && (b `impl` a)
    ONot a -> not a
    OLit x -> x


evalPropGeneral :: (Applicative f) => (PropOp r -> r) -> (a -> f r) -> Prop a -> f r
evalPropGeneral eval evalEmbedded = \case
  SOp op -> eval <$> traverse (evalPropGeneral eval evalEmbedded) op
  SVar x -> evalEmbedded x


evalPropBool :: (Applicative f) => (a -> f Bool) -> Prop a -> f Bool
evalPropBool = evalPropGeneral evalOpBool


pattern PAnd :: Prop t -> Prop t -> Prop t
pattern PAnd a b = SOp (OAnd a b)

pattern POr :: Prop t -> Prop t -> Prop t
pattern POr a b = SOp (OOr a b)

pattern PImpl :: Prop t -> Prop t -> Prop t
pattern PImpl a b = SOp (OImpl a b)

pattern PEquiv :: Prop t -> Prop t -> Prop t
pattern PEquiv a b = SOp (OEquiv a b)

pattern PNot :: Prop t -> Prop t
pattern PNot a = SOp (ONot a)
