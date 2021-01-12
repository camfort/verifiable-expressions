{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}

module Language.Expression.GeneralOp where

-- import           Data.Typeable

import           Data.Vinyl
-- import           Data.Vinyl.Functor
-- import           Data.Vinyl.TypeLevel

import           Language.Expression
import           Language.Expression.Pretty

data GeneralOp op t a where
  Op :: RMap as => op as r -> Rec t as -> GeneralOp op t r

class EvalOpAt k op where
  evalMany :: op as r -> Rec k as -> k r

-- class EqOpMany op where
--   liftEqMany
--     :: op as a -> op bs b

--     -> (forall xs. (AllConstrained Eq xs, RecApplicative xs) =>
--         Rec f xs -> Rec g xs -> Bool)

--     -> Rec f as -> Rec g bs -> Bool


class PrettyOp op where
  prettysPrecOp :: Pretty1 t => Int -> op as a -> Rec t as -> ShowS

instance HFunctor (GeneralOp op) where

instance HTraversable (GeneralOp op) where
  htraverse f = \case
    Op o args -> Op o <$> rtraverse f args


instance (EvalOpAt k op) => HFoldableAt k (GeneralOp op) where
  hfoldMap f = \case
    Op o args -> evalMany o (rmap f args)


-- instance EqOpMany op => HEq (GeneralOp op) where
--   liftHEq le _ (Op o1 (xs :: Rec f as)) (Op o2 (ys :: Rec g bs)) =
--     liftEqMany o1 o2 liftEqAll xs ys

--     where
--       liftEqAll
--         :: (AllConstrained Eq xs, RecApplicative xs)
--         => Rec f xs -> Rec g xs -> Bool
--       liftEqAll (xs' :: Rec f xs) ys' =
--         let
--           eqList :: Rec (Lift (->) f (Lift (->) g (Const Bool))) xs
--           eqList = rpureConstrained (Proxy :: Proxy Eq)
--             (Lift $ \x -> Lift $ Const . le (==) x)
--         in and . recordToList $ eqList <<*>> xs' <<*>> ys'

instance PrettyOp op => Pretty2 (GeneralOp op) where
  prettys2Prec p = \case
    Op op args -> prettysPrecOp p op args
