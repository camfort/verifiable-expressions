{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeOperators             #-}

module Language.Expression.Lambda where

import           Data.Semigroup            (Max (..))

import           Data.Typeable             ((:~:) (..), Typeable, eqT)

import           Control.Lens

import           Language.Expression
import           Language.Expression.Scope

data LambdaOp s t a where
  App :: t (a -> b) -> t a -> LambdaOp s t b

  -- | Abstracts a scope where bound variables are in the @(':~:') a@ functor,
  -- meaning they have the same type as @a@. Free variables ignore the argument
  -- and have type @b@.
  Abs :: s ((:~:) a) b -> LambdaOp s t (a -> b)

instance HDuofunctor LambdaOp where
  hduomap = defaultHduomap

instance HDuotraversable LambdaOp where
  hduotraverse f g = \case
    App x y -> App <$> g x <*> g y
    Abs x -> Abs <$> f pure x

instance HFunctor (LambdaOp s) where
  hmap f = \case
    App x y -> App (f x) (f y)
    Abs x -> Abs x

instance (HTraversable s) => HTraversable (LambdaOp s) where
  htraverse = hduotraverseSecond

instance HDuofoldableAt Identity LambdaOp where
  hduofoldMapAt f = \case
    App (Identity g) (Identity x) -> Identity (g x)
    Abs y -> Identity (\x -> runIdentity (f (\Refl -> Identity x) y))


type LambdaExpr = SFree LambdaOp

-- var :: v a -> LambdaExpr

app :: LambdaExpr v (a -> b) -> LambdaExpr v a -> LambdaExpr v b
app f x = SWrap (App f x)

-- newtype Scope g h f a = Scope { unscope :: h (BV g (h f)) a }

lam' :: Scope ((:~:) a) LambdaExpr v b -> LambdaExpr v (a -> b)
lam' = SWrap . Abs . Scoped


data TVar k a where
  TVar :: Typeable a => { tvarKey :: k } -> TVar k a


uniqueTVarKey :: (HTraversable h, Ord k, Bounded k, Enum k) => h (TVar k) a -> k
uniqueTVarKey x =
  let Max highestUsed = hfoldMap (Max . tvarKey) x
  in succ highestUsed


abstractTVar :: (HMonad h, Typeable a, Eq k) => k -> h (TVar k) b -> Scope ((:~:) a) h (TVar k) b
abstractTVar nm = abstract (\case TVar nm' | nm == nm' -> eqT
                                  _ -> Nothing)

-- abstractTVar'
--   :: (HMonad h, HTraversable h, Typeable a, Ord k, Bounded k, Enum k, Typeable b)
--   => h (TVar k) b -> Scope ((:~:) a) h (TVar k) b
-- abstractTVar' x = abstractTVar (uniqueTVarKey x) x

-- -- | "Wow! This works?"
-- lam :: (Ord k, Bounded k, Enum k, Typeable a, Typeable b) => (LambdaExpr (TVar k) a -> LambdaExpr (TVar k) b) -> LambdaExpr (TVar k) (a -> b)
-- lam f =
--   let k = uniqueTVarKey
--   -- lam' $ abstractTVar' $ f _
