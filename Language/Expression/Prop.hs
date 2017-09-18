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

import           Data.Monoid                (All (..), Any (..))

import           Data.Functor.Compose
import           Data.Functor.Identity

import           Data.SBV
import           Data.SBV.Internals (SBV(..))

import           Language.Expression
import           Language.Expression.Util
import           Language.Expression.Scope
import qualified Language.Expression.Prop.Simple as S


type Prop = SFree BPOp

--------------------------------------------------------------------------------
--  DSL
--------------------------------------------------------------------------------

-- infixl 3 *&&
-- infixl 2 *||
-- infixr 1 *->
-- infix 1 *<->

-- | Lift an expression into the land of propositions.
expr :: expr a -> Prop expr a
expr = SPure

plit :: Bool -> Prop expr Bool
plit = SWrap . BPSimple . S.LogLit

pnot :: Prop expr Bool -> Prop expr Bool
pnot = SWrap . BPSimple . S.LogNot

(*&&) :: Prop expr Bool -> Prop expr Bool -> Prop expr Bool
(*&&) = SWrap ... BPSimple ... S.LogAnd

(*||) :: Prop expr Bool -> Prop expr Bool -> Prop expr Bool
(*||) = SWrap ... BPSimple ... S.LogOr

(*->) :: Prop expr Bool -> Prop expr Bool -> Prop expr Bool
(*->) = SWrap ... BPSimple ... S.LogImpl

(*<->) :: Prop expr Bool -> Prop expr Bool -> Prop expr Bool
(*<->) = SWrap ... BPSimple ... S.LogEquiv


data AbsExpr a expr b where
  AbsExpr :: expr b -> AbsExpr a expr b
  AbsVar :: String -> AbsExpr a expr a

instance HFunctor (AbsExpr a)
instance HTraversable (AbsExpr a) where
  htraverse f = \case
    AbsExpr x -> AbsExpr <$> f x
    AbsVar s -> pure (AbsVar s)


absBinder1 :: (Finite a) => Prop (AbsExpr a expr) b -> Scope (BPBinderEnumerable a) Prop expr b
absBinder1
  = Scope
  . hmap (\case AbsExpr x -> F (expr x)
                AbsVar _ -> B BPBinderEnumerable
         )

data HCompose h h' t a where
  HCompose :: h (h' t) a -> HCompose h h' t a

absBinder2 :: Prop (Scope (BPBinderEnumerable a) expr v) b -> Scope (BPBinderEnumerable a) (HCompose Prop expr) v b
absBinder2 = Scope . hmap _

-- abstract f = Scope . hmap (\y -> maybe ((hpure . hpure) y) B $ f y)


pforall :: String -> Prop (Scope (BPBinderEnumerable a) expr v) b -> Prop (expr v) Bool
pforall nm f = undefined


--------------------------------------------------------------------------------
--  Operators
--------------------------------------------------------------------------------

data BPBinderEnumerable a b where
  BPBinderEnumerable :: Finite a => BPBinderEnumerable a a

data BPBinderType = BForall | BExists
  deriving (Eq, Ord, Show, Read)


data BPBinder s t b where
  BPBind :: BPBinderType -> s (Compose t (BPBinderEnumerable a)) Bool -> BPBinder s t Bool


instance HDuofunctor BPBinder
instance HDuotraversable BPBinder where
  hduotraverse g f = \case
    BPBind bt y -> BPBind bt <$> g (\(Compose z) -> Compose <$> f z) y


instance HDuofoldableAt Identity BPBinder where
  hduofoldMap = implHduofoldMap $ \g -> \case
    BPBind bt y ->
      Identity $ foldBT (runIdentity . g id) $
      htraverse (\(Compose (Identity BPBinderEnumerable)) ->
                   Identity <$> enumAll) y
      where
        foldBT :: (a -> Bool) -> [a] -> Bool
        foldBT f = case bt of
          BForall -> getAll . foldMap (All . f)
          BExists -> getAny . foldMap (Any . f)

data SBVProp a where
  SBVEnumerable :: SymWord a => String -> SBVProp (BPBinderEnumerable a a)
  SBVTerm :: SBV a -> SBVProp a


instance HDuofoldableAt (Compose Symbolic SBVProp) BPBinder where
  hduofoldMap = implHduofoldMapCompose $ \g -> \case
    BPBind bt y ->
      g getCompose $
      hmap (\(Compose (SBVEnumerable nm)) ->
              let sym = case bt of
                    BForall -> forall nm
                    BExists -> exists nm
              in Compose (SBVTerm <$> sym)
           ) y


data BPOp s t a where
  BPBinder :: BPBinder s t Bool -> BPOp s t Bool
  BPSimple :: S.LogicOp t a -> BPOp s t a

instance HDuofunctor BPOp
instance HDuotraversable BPOp where
  hduotraverse g f = \case
    BPBinder x -> BPBinder <$> hduotraverse g f x
    BPSimple x -> BPSimple <$> htraverse f x

instance HDuofoldableAt Identity BPOp where
  hduofoldMap g f = \case
    BPBinder x -> hduofoldMap g f x
    BPSimple x -> hfoldMap f x


instance HFoldableAt (Compose Symbolic SBVProp) S.LogicOp where
  hfoldMap = implHfoldMapCompose $ \x ->
    let x' = hmap (\(SBVTerm y) -> y) x
    in return . SBVTerm $ hfold x'


instance HDuofoldableAt (Compose Symbolic SBVProp) BPOp where
  hduofoldMap g f = \case
    BPBinder x -> hduofoldMap g f x
    BPSimple x -> hfoldMap f x



class (Enum a, Bounded a) => Finite a where
  enumAll :: [a]
  enumAll = [minBound .. maxBound]
instance (Enum a, Bounded a) => Finite a
