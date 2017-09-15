{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeOperators             #-}

module Language.Expression.Lambda where

import           Data.Typeable             ((:~:) (..), Typeable, eqT)

import           Control.Lens

import           Language.Expression
import           Language.Expression.Scope

data LambdaOp s t a where
  App :: t (a -> b) -> t a -> LambdaOp s t b

  -- | Abstracts a scope where bound variables are in the @(':~:') a@ functor,
  -- meaning they have the type @a@. Free variables ignore the argument and have
  -- type @b@.
  Abs :: s ((:~:) a) b -> LambdaOp s t (a -> b)

  Add :: (Num a) => t a -> t a -> LambdaOp s t a

instance HDuofunctor LambdaOp where
instance HDuotraversable LambdaOp where
  hduotraverse f g = \case
    App x y -> App <$> g x <*> g y
    Abs x -> Abs <$> f pure x
    Add x y -> Add <$> g x <*> g y

instance (HTraversable s) => HFunctor (LambdaOp s) where

instance (HTraversable s) => HTraversable (LambdaOp s) where
  htraverse = hduotraverseSecond

instance HDuofoldableAt Identity LambdaOp where
  hduofoldMap g f = \case
    App h x -> f h <*> f x
    Abs y -> Identity (\x -> runIdentity (g (\Refl -> Identity x) y))
    Add x y -> (+) <$> f x <*> f y


type LambdaExpr = SFree LambdaOp

var' :: v a -> LambdaExpr v a
var' = SPure

app :: LambdaExpr v (a -> b) -> LambdaExpr v a -> LambdaExpr v b
app f x = SWrap (App f x)

-- newtype Scope g h f a = Scope { unscope :: h (BV g (h f)) a }

lam' :: Scope ((:~:) a) LambdaExpr v b -> LambdaExpr v (a -> b)
lam' = SWrap . Abs . Scoped


data TVar k a where
  TVar :: Typeable a => { tvarKey :: k } -> TVar k a


abstractTVar :: (HMonad h, Typeable a, Eq k) => k -> h (TVar k) b -> Scope ((:~:) a) h (TVar k) b
abstractTVar nm = abstract $ \case
  TVar nm' | nm == nm' -> eqT
  _ -> Nothing

lam :: (Eq k, Typeable a, Typeable b) => k -> LambdaExpr (TVar k) b -> LambdaExpr (TVar k) (a -> b)
lam k x = lam' (abstractTVar k x)


var :: (Typeable a) => k -> LambdaExpr (TVar k) a
var = var' . TVar


(.+) :: (Num a) => LambdaExpr v a -> LambdaExpr v a -> LambdaExpr v a
x .+ y = SWrap (Add x y)



example :: LambdaExpr (TVar String) (Int -> Float -> Float -> Float)
example = lam "x" $ lam "y" $ lam "z" $ var "y" .+ var "z"


eval :: LambdaExpr v a -> a
eval = runIdentity . hfoldMap (const (error "can't evaluate with free variables"))
