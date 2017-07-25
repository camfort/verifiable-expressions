{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE PatternSynonyms    #-}

module Language.While.Prop where

import           Control.Monad (ap)
import           Data.Data

data PropOp a
  = OAnd a a
  | OOr a a
  | OImpl a a
  | OEquiv a a
  | ONot a
  deriving (Show, Eq, Ord, Data, Typeable, Functor, Foldable, Traversable)

data Prop a
  = POp (PropOp (Prop a))
  -- ^ An operator combining two propositions.
  | PLit Bool
  -- ^ A literal truth value.
  | PEmbed a
  -- ^ An embedded value, for example a variable or some kind of atomic
  -- expression.
  deriving (Show, Eq, Ord, Data, Typeable, Functor, Foldable, Traversable)


instance Applicative Prop where
  pure = return
  (<*>) = ap


-- | If the embedded values are variables, monad bind performs substitution.
instance Monad Prop where
  return = PEmbed

  prop >>= f = case prop of
    POp op -> POp (fmap (>>= f) op)
    PLit b -> PLit b
    PEmbed a -> f a


evalOpBool :: PropOp Bool -> Bool
evalOpBool =
  let impl a b = not a || b
  in \case
    OAnd a b -> a && b
    OOr a b -> a || b
    OImpl a b -> a `impl` b
    OEquiv a b -> (a `impl` b) && (b `impl` a)
    ONot a -> not a


evalPropGeneral :: (Applicative f) => (PropOp r -> r) -> (Bool -> r) -> (a -> f r) -> Prop a -> f r
evalPropGeneral evalOp liftBool evalEmbedded = \case
  POp op -> evalOp <$> traverse (evalPropGeneral evalOp liftBool evalEmbedded) op
  PLit b -> pure (liftBool b)
  PEmbed x -> evalEmbedded x


evalPropBool :: (Applicative f) => (a -> f Bool) -> Prop a -> f Bool
evalPropBool = evalPropGeneral evalOpBool id


pattern PAnd :: Prop t -> Prop t -> Prop t
pattern PAnd a b = POp (OAnd a b)

pattern POr :: Prop t -> Prop t -> Prop t
pattern POr a b = POp (OOr a b)

pattern PImpl :: Prop t -> Prop t -> Prop t
pattern PImpl a b = POp (OImpl a b)

pattern PEquiv :: Prop t -> Prop t -> Prop t
pattern PEquiv a b = POp (OEquiv a b)

pattern PNot :: Prop t -> Prop t
pattern PNot a = POp (ONot a)
