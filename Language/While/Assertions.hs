{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.While.Assertions where

import           Data.Functor.Compose

import           Data.SBV                   (SBV)
import qualified Data.SBV                   as S

import           Language.While.Expressions

--------------------------------------------------------------------------------
--  Generalised Prelude Classes
--------------------------------------------------------------------------------

class SymBool b where
  fromBool :: Bool -> b

  (.&&) :: b -> b -> b
  bnot :: b -> b

  (.||) :: b -> b -> b
  a .|| b = bnot (bnot a .&& bnot b)

class SymBool b => SymEq b a where
  (.==) :: a -> a -> b
  x .== y = bnot (x ./= y)

  (./=) :: a -> a -> b
  x ./= y = bnot (x .== y)

class (SymEq b a, SymBool b) => SymOrd b a where
  (.<) :: a -> a -> b
  x .< y = bnot (x .> y)

  (.<=) :: a -> a -> b
  x .<= y = bnot (x .>= y)

  (.>) :: a -> a -> b
  x .> y = bnot (x .< y)

  (.>=) :: a -> a -> b
  x .>= y = bnot (x .<= y)

-- instance S.OrdSymbolic a => SymOrd S.SBool a where
--   (.<) = (S..<)
--   (.<=) = (S..<=)

--------------------------------------------------------------------------------
--  Operators
--------------------------------------------------------------------------------

data BoolOp t a where
  OpNot :: SymBool b => t b -> BoolOp t b
  OpAnd :: SymBool b => t b -> t b -> BoolOp t b
  OpOr :: SymBool b => t b -> t b -> BoolOp t b

data NumOp t a where
  OpAdd :: Num a => t a -> t a -> NumOp t a
  OpSub :: Num a => t a -> t a -> NumOp t a

data LitOp (t :: * -> *) a where
  OpLit :: a -> LitOp t a

data EqOp t a where
  OpEq :: SymEq b a => t a -> t a -> EqOp t b

data OrdOp t a where
  OpLT :: SymOrd b a => t a -> t a -> OrdOp t b
  OpLE :: SymOrd b a => t a -> t a -> OrdOp t b
  OpGT :: SymOrd b a => t a -> t a -> OrdOp t b
  OpGE :: SymOrd b a => t a -> t a -> OrdOp t b

instance Operator BoolOp where
  traverseOp f = \case
    OpNot x -> OpNot <$> f x
    OpAnd x y -> OpAnd <$> f x <*> f y
    OpOr x y -> OpOr <$> f x <*> f y

  evalOp = \case
    OpNot x -> bnot <$> x
    OpAnd x y -> (.&&) <$> x <*> y
    OpOr x y -> (.||) <$> x <*> y

instance Operator NumOp where
  traverseOp f = \case
    OpAdd x y -> OpAdd <$> f x <*> f y
    OpSub x y -> OpSub <$> f x <*> f y

  evalOp = \case
    OpAdd x y -> (+) <$> x <*> y
    OpSub x y -> (-) <$> x <*> y

instance Operator LitOp where
  traverseOp _ = \case
    OpLit x -> pure (OpLit x)

  evalOp = \case
    OpLit x -> pure x

instance Operator EqOp where
  traverseOp f = \case
    OpEq x y -> OpEq <$> f x <*> f y

  evalOp = \case
    OpEq x y -> (.==) <$> x <*> y

instance Operator OrdOp where
  traverseOp f = \case
    OpLT x y -> OpLT <$> f x <*> f y
    OpLE x y -> OpLE <$> f x <*> f y
    OpGT x y -> OpGT <$> f x <*> f y
    OpGE x y -> OpGE <$> f x <*> f y

  evalOp = \case
    OpLT x y -> (.<) <$> x <*> y
    OpLE x y -> (.<=) <$> x <*> y
    OpGT x y -> (.>) <$> x <*> y
    OpGE x y -> (.>=) <$> x <*> y

type BasicOp = LitOp :+: (BoolOp :+: NumOp) :+: (EqOp :+: OrdOp)

--------------------------------------------------------------------------------
--  Expressions
--------------------------------------------------------------------------------

-- | @'PropOn' expr a@ is the type of @a@-valued propositions over expressions
-- of type @expr@.
type PropOn = Expr BoolOp

--------------------------------------------------------------------------------
--  SBV Instances
--------------------------------------------------------------------------------

instance SymBool b => S.Boolean b where
  true = fromBool True
  bnot = bnot
  (&&&) = (.&&)

instance SymBool b => SymBool (SBV b) where
  fromBool = S.fromBool
  bnot = S.bnot
  (.&&) = (S.&&&)

instance HoistOp SBV BoolOp where
  hoistOp' = \case
    OpNot x -> OpNot (getCompose x)
    OpAnd x y -> OpAnd (getCompose x) (getCompose y)
    OpOr x y -> OpOr (getCompose x) (getCompose y)

instance SymEq (SBV Bool) a => S.EqSymbolic a where
  (.==) = (.==)

-- instance SymEq (SBV Bool) a => SymEq (SBV Bool) (SBV a) where
--   (.==) = (S..==)

instance HoistOp SBV EqOp where
  hoistOp' = \case
    OpEq x y -> OpEq (getCompose x) (getCompose y)
