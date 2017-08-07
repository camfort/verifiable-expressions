{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ScopedTypeVariables         #-}

module Language.Expression.Ops.General where

import           Data.Typeable

import           Data.Vinyl
import           Data.Vinyl.Functor
import           Data.Vinyl.TypeLevel

import           Language.Expression
import           Language.Expression.Pretty

data GeneralOp op t a where
  Op :: op as r -> Rec t as -> GeneralOp op t r

class EvalOpMany m k op where
  evalMany :: op as r -> Rec k as -> m (k r)

class EqOpMany op where
  liftEqMany
    :: op as a -> op bs b

    -> (forall xs. (AllConstrained Eq xs, RecApplicative xs) =>
        Rec f xs -> Rec g xs -> Bool)

    -> Rec f as -> Rec g bs -> Bool


class PrettyOpMany op where
  prettysPrecMany :: Pretty1 t => Int -> op as a -> Rec t as -> ShowS


instance Operator (GeneralOp op) where
  htraverseOp f = \case
    Op o args -> Op o <$> rtraverse f args


instance (Monad m, EvalOpMany m k op) => EvalOp m k (GeneralOp op) where
  evalOp f = \case
    Op o args -> rtraverse f args >>= evalMany o


instance EqOpMany op => HEq (GeneralOp op) where
  liftHEq le _ (Op o1 (xs :: Rec f as)) (Op o2 (ys :: Rec g bs)) =
    liftEqMany o1 o2 liftEqAll xs ys

    where
      liftEqAll
        :: (AllConstrained Eq xs, RecApplicative xs)
        => Rec f xs -> Rec g xs -> Bool
      liftEqAll (xs' :: Rec f xs) ys' =
        let
          eqList :: Rec (Lift (->) f (Lift (->) g (Const Bool))) xs
          eqList = rpureConstrained (Proxy :: Proxy Eq)
            (Lift $ \x -> Lift $ Const . le (==) x)
        in and . recordToList $ eqList <<*>> xs' <<*>> ys'

instance PrettyOpMany op => Pretty2 (GeneralOp op) where
  prettys2Prec p = \case
    Op op args -> prettysPrecMany p op args
