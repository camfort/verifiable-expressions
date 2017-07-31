{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Verification.Expression.Operators
  (
  -- * Standard operators
    BoolOp(..)
  , EqOp(..)
  , OrdOp(..)
  , LitOp(..)
  , NumOp(..)

  -- * Propositions
  , PropOn

  -- * Basic Operators
  , BasicOp
  , bLit
  , bNot
  , bAnd
  , bOr
  , bAdd
  , bSub
  , bMul
  , bEq
  , bLT
  , bLE
  , bGT
  , bGE
  ) where

import           Data.SBV                         (SBV)
import           Language.Verification.Expression
import           Language.Verification.SymClasses

--------------------------------------------------------------------------------
--  Operators
--------------------------------------------------------------------------------

data BoolOp t a where
  OpNot :: SymBool b => t b -> BoolOp t b
  OpAnd :: SymBool b => t b -> t b -> BoolOp t b
  OpOr :: SymBool b => t b -> t b -> BoolOp t b
  OpImpl :: SymBool b => t b -> t b -> BoolOp t b
  OpEquiv :: SymBool b => t b -> t b -> BoolOp t b

data NumOp t a where
  OpAdd :: SymNum a => t a -> t a -> NumOp t a
  OpSub :: SymNum a => t a -> t a -> NumOp t a
  OpMul :: SymNum a => t a -> t a -> NumOp t a

data LitOp (t :: * -> *) a where
  OpLit :: SymValue a => a -> LitOp t a

data EqOp t a where
  OpEq :: SymEq b a => t a -> t a -> EqOp t b

data OrdOp t a where
  OpLT :: SymOrd b a => t a -> t a -> OrdOp t b
  OpLE :: SymOrd b a => t a -> t a -> OrdOp t b
  OpGT :: SymOrd b a => t a -> t a -> OrdOp t b
  OpGE :: SymOrd b a => t a -> t a -> OrdOp t b

instance Operator BoolOp where
  htraverseOp f = \case
    OpNot x -> OpNot <$> f x
    OpAnd x y -> OpAnd <$> f x <*> f y
    OpOr x y -> OpOr <$> f x <*> f y
    OpImpl x y -> OpImpl <$> f x <*> f y
    OpEquiv x y -> OpEquiv <$> f x <*> f y

  evalOp = \case
    OpNot x -> symNot <$> x
    OpAnd x y -> symAnd <$> x <*> y
    OpOr x y -> symOr <$> x <*> y
    OpImpl x y -> symImpl <$> x <*> y
    OpEquiv x y -> symEquiv <$> x <*> y

instance Operator NumOp where
  htraverseOp f = \case
    OpAdd x y -> OpAdd <$> f x <*> f y
    OpSub x y -> OpSub <$> f x <*> f y
    OpMul x y -> OpMul <$> f x <*> f y

  evalOp = \case
    OpAdd x y -> symAdd <$> x <*> y
    OpSub x y -> symSub <$> x <*> y
    OpMul x y -> symMul <$> x <*> y

instance Operator LitOp where
  htraverseOp _ = \case
    OpLit x -> pure (OpLit x)

  evalOp = \case
    OpLit x -> pure x

instance Operator EqOp where
  htraverseOp f = \case
    OpEq x y -> OpEq <$> f x <*> f y

  evalOp = \case
    OpEq x y -> symEq <$> x <*> y

instance Operator OrdOp where
  htraverseOp f = \case
    OpLT x y -> OpLT <$> f x <*> f y
    OpLE x y -> OpLE <$> f x <*> f y
    OpGT x y -> OpGT <$> f x <*> f y
    OpGE x y -> OpGE <$> f x <*> f y

  evalOp = \case
    OpLT x y -> symLt <$> x <*> y
    OpLE x y -> symLe <$> x <*> y
    OpGT x y -> symGt <$> x <*> y
    OpGE x y -> symGe <$> x <*> y

type BasicOp = OpChoice '[LitOp, BoolOp, NumOp, EqOp, OrdOp]

bLit :: SymValue a => a -> BasicOp t a
bLit x = Op0 (OpLit x)

bNot :: SymBool a => t a -> BasicOp t a
bNot x = Op1 (OpNot x)

bAnd :: SymBool a => t a -> t a -> BasicOp t a
bAnd x y = Op1 (OpAnd x y)

bOr :: SymBool a => t a -> t a -> BasicOp t a
bOr x y = Op1 (OpOr x y)

bAdd :: SymNum a => t a -> t a -> BasicOp t a
bAdd x y = Op2 (OpAdd x y)

bSub :: SymNum a => t a -> t a -> BasicOp t a
bSub x y = Op2 (OpSub x y)

bMul :: SymNum a => t a -> t a -> BasicOp t a
bMul x y = Op2 (OpMul x y)

bEq :: SymEq b a => t a -> t a -> BasicOp t b
bEq x y = Op3 (OpEq x y)

bLT :: SymOrd b a => t a -> t a -> BasicOp t b
bLT x y = Op4 (OpLT x y)

bLE :: SymOrd b a => t a -> t a -> BasicOp t b
bLE x y = Op4 (OpLE x y)

bGT :: SymOrd b a => t a -> t a -> BasicOp t b
bGT x y = Op4 (OpGT x y)

bGE :: SymOrd b a => t a -> t a -> BasicOp t b
bGE x y = Op4 (OpGE x y)

--------------------------------------------------------------------------------
--  Expressions
--------------------------------------------------------------------------------

-- | @'PropOn' expr a@ is the type of @a@-valued propositions over expressions
-- of type @expr@.
type PropOn = Expr BoolOp

--------------------------------------------------------------------------------
--  HoistOp SBV Instances
--------------------------------------------------------------------------------

instance HoistOp SBV BoolOp where
  hoistOp f = \case
    OpNot x -> OpNot (f x)
    OpAnd x y -> OpAnd (f x) (f y)
    OpOr x y -> OpOr (f x) (f y)
    OpImpl x y -> OpImpl (f x) (f y)
    OpEquiv x y -> OpEquiv (f x) (f y)

instance HoistOp SBV EqOp where
  hoistOp f = \case
    OpEq x y -> OpEq (f x) (f y)

instance HoistOp SBV OrdOp where
  hoistOp f = \case
    OpLT x y -> OpLT (f x) (f y)
    OpLE x y -> OpLE (f x) (f y)
    OpGT x y -> OpGT (f x) (f y)
    OpGE x y -> OpGE (f x) (f y)

instance HoistOp SBV LitOp where
  hoistOp _ = \case
    OpLit x -> OpLit (layerSymbolic x)

instance HoistOp SBV NumOp where
  hoistOp f = \case
    OpAdd x y -> OpAdd (f x) (f y)
    OpSub x y -> OpSub (f x) (f y)
    OpMul x y -> OpMul (f x) (f y)
