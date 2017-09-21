{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

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

import           Data.Monoid (All(..))

import           Data.Functor.Compose
import           Data.Functor.Identity

import           Data.SBV
import           Data.SBV.Internals (SBV(..))

import           Language.Expression
import           Language.Expression.Util
import           Language.Expression.Scope
import qualified Language.Expression.Prop.Simple as S

--------------------------------------------------------------------------------
--  Propositions
--------------------------------------------------------------------------------

-- data Prop expr v a where
--   PropExpr :: Scope g expr v a -> Prop expr v a

-- type Prop = SFree PropOp

-- --------------------------------------------------------------------------------
-- --  DSL
-- --------------------------------------------------------------------------------

-- infixl 3 *&&
-- infixl 2 *||
-- infixr 1 *->
-- infix 1 *<->

-- -- | Lift an expression into the land of propositions.
-- expr :: expr a -> Prop expr a
-- expr = SPure

-- plit :: Bool -> Prop expr Bool
-- plit = SWrap . PopSimple . S.LogLit

-- pnot :: Prop expr Bool -> Prop expr Bool
-- pnot = SWrap . PopSimple . S.LogNot

-- (*&&) :: Prop expr Bool -> Prop expr Bool -> Prop expr Bool
-- (*&&) = SWrap ... PopSimple ... S.LogAnd

-- (*||) :: Prop expr Bool -> Prop expr Bool -> Prop expr Bool
-- (*||) = SWrap ... PopSimple ... S.LogOr

-- (*->) :: Prop expr Bool -> Prop expr Bool -> Prop expr Bool
-- (*->) = SWrap ... PopSimple ... S.LogImpl

-- (*<->) :: Prop expr Bool -> Prop expr Bool -> Prop expr Bool
-- (*<->) = SWrap ... PopSimple ... S.LogEquiv


-- pforall :: (HFunctor expr) => Prop (Scope (Enumerable a) expr v) Bool -> Prop (expr v) Bool
-- pforall = SWrap . PopForall . Scoped . _

--------------------------------------------------------------------------------
--  Operators
--------------------------------------------------------------------------------

data Enumerable a b where
  Enumerable :: (SymWord a, Finite a) => Enumerable a a

data PropOp s t a where
  PopForall :: s (Enumerable a) Bool -> PropOp s t Bool
  PopSimple :: S.LogicOp t a -> PropOp s t a

--------------------------------------------------------------------------------
--  Instances
--------------------------------------------------------------------------------

instance HDuofunctor PropOp
instance HDuotraversable PropOp where
  hduotraverse g f = \case
    PopForall x -> PopForall <$> g pure x
    PopSimple x -> PopSimple <$> htraverse f x

instance HFunctor s => HFunctor (PropOp s) where
  hmap = hduomapSecond
instance HTraversable s => HTraversable (PropOp s) where
  htraverse = hduotraverseSecond

instance HDuofoldableAt Identity PropOp where
  hduofoldMap =
    implHduofoldMap $ \g -> \case
      PopForall x ->
        fmap getAll .
        foldMap @[] (fmap All . g id) .
        htraverse (\Enumerable -> Identity <$> enumAll) $
        x
      PopSimple x -> hfold x


instance HDuofoldableAt (Compose Symbolic SBV) PropOp where
  hduofoldMap = implHduofoldMapCompose $ \g -> \case
    PopForall x -> g (\Enumerable -> forall_) x
    PopSimple x -> pure (hfold x)


class (Enum a, Bounded a) => Finite a where
  enumAll :: [a]
  enumAll = [minBound .. maxBound]

--------------------------------------------------------------------------------
--  Util
--------------------------------------------------------------------------------

-- rescope :: (HFunctor h) => Scope g h f a -> Scope g (SFree h') (h f) a
-- rescope (Scope x) = Scope (SPure _)


-- x :: h (BV g (h f)) a
