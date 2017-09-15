{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

{-|

Propositions and combinators for conveniently constructing them.

-}
module Language.Expression.Prop where
  -- (
  --   -- * Proposition Types
  --   Prop
  -- , Prop'
  --   -- * DSL
  -- , expr
  -- , plit
  -- , pnot
  -- , (*&&)
  -- , (*||)
  -- , (*->)
  -- , (*<->)
  -- , propAnd
  -- , propOr
  --   -- * HTraversable
  -- , LogicOp(..)
  -- ) where

import           Control.Applicative        (liftA2)
import           Data.List                  (foldl')
import           Data.Typeable

-- import           Data.Functor.Classes
import           Data.Distributive
import           Data.Functor.Identity
import           Data.Functor.Compose

import           Data.Vinyl                 hiding ((:~:))
import           Data.Vinyl.TypeLevel

import           Data.SBV

import           Language.Expression
import           Language.Expression.Choice
import           Language.Expression.Func
import           Language.Expression.Pretty
import           Language.Expression.Scope
import           Language.Expression.Util


type BoundVar a = (:~:) a


instance HDuofunctor (BindingOp c)
instance HDuotraversable (BindingOp c) where
  hduotraverse g f = \case
    BopLift x -> BopLift <$> f x
    BopBind x -> BopBind <$> g pure x

instance HFunctor (BindingOp c s) where
instance HTraversable (BindingOp c s) where
  htraverse f = \case
    BopLift x -> BopLift <$> f x
    BopBind x -> pure $ BopBind x

-- The same implementation works for any @t@ with @Applicative t, Distributive t@.
instance HDuofoldableAt Identity (BindingOp c) where
  hduofoldMap g f = \case
    BopLift x -> pure <$> f x
    BopBind y ->
      fmap Func . distribute $ \(Identity x :& args) -> (`appF` args) <$> g (\Refl -> pure x) y

-- instance HDuofoldableAt (Compose Symbolic SBVFunc) (BindingOp SymWord) where
--   hduofoldMap = implHduofoldMapCompose $ \g -> \case
--     BopLift (SBVVal x) -> pure (SBVFunc (pure x))
--     BopBind y -> do
--       SBVFunc (Func y') <- g _ y
--       return $ SBVFunc . Func $ \(x :& args) -> _


instance HFunctor QuantifierOp
instance HTraversable QuantifierOp where
  htraverse f = \case
    QopForall x -> QopForall <$> f x
    QopExists x -> QopExists <$> f x


data SBVFunc a where
  SBVFunc :: (SymWord result, AllConstrained SymWord args) => Func' SBV args (SBV result) -> SBVFunc (Func args result)
  SBVVal :: (SymWord a) => SBV a -> SBVFunc a


instance HFoldableAt (Compose Symbolic SBVFunc) QuantifierOp where
  hfoldMap = implHfoldMapCompose $ \case
    QopForall (SBVFunc func) -> SBVFunc . appF1 func <$> forall_
    QopForall (SBVVal _) -> error "impossible"
    QopExists (SBVFunc func) -> SBVFunc . appF1 func <$> exists_
    QopExists (SBVVal _) -> error "impossible"



data BindingOp c s t a where
  BopLift :: AllConstrained c args => t b -> BindingOp c s t (Func args b)
  BopBind :: (c a, AllConstrained c args, c b) => s (BoundVar a) (Func args b) -> BindingOp c s t (Func (a ': args) b)


data QuantifierOp t a where
  QopForall :: t (Func (a ': args) Bool) -> QuantifierOp t (Func args Bool)
  QopExists :: t (Func (a ': args) Bool) -> QuantifierOp t (Func args Bool)
