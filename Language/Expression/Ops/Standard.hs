{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeOperators              #-}

{-|

A collection of standard operator types which may be used to form expressions.

-}
module Language.Expression.Ops.Standard
  (
  -- * Standard operators
    LogicOp(..)

  -- * Evaluating purely
  , PureEval(..)

  -- * Expression and operator type classes
  , module Expression

  -- * Classes used to constrain operator types
  , module Classes
  ) where

import           Control.Applicative             (liftA2)
import           Data.Functor.Classes
import           Data.Functor.Compose
import           Data.Typeable                   ((:~:) (..), Typeable, eqT)

import           Data.SBV                        (SBV)
import qualified Data.SBV                        as S

import           Language.Expression             as Expression
import           Language.Expression.Ops.Classes as Classes

--------------------------------------------------------------------------------
--  Operators
--------------------------------------------------------------------------------

{-| A newtype wrapper to evaluate operators in a pure context.

e.g.

@
getPureEval . evalOp' PureEval :: Expr' StandardOps Maybe a -> Maybe a
@

Notice this expression contains variables in 'Maybe', which actually means that
"variables" have been substituted for literal values that may or may not exist.

-}
newtype PureEval f a = PureEval { getPureEval :: f a }
  deriving (Functor, Applicative, Monad)

-- | Logical operations
data LogicOp t a where
  LogLit :: Bool -> LogicOp t Bool
  LogNot :: t Bool -> LogicOp t Bool
  LogAnd :: t Bool -> t Bool -> LogicOp t Bool
  LogOr :: t Bool -> t Bool -> LogicOp t Bool
  LogImpl :: t Bool -> t Bool -> LogicOp t Bool
  LogEquiv :: t Bool -> t Bool -> LogicOp t Bool

instance Operator LogicOp where
  htraverseOp f = \case
    LogLit b -> pure $ LogLit b
    LogNot x -> LogNot <$> f x
    LogAnd x y -> LogAnd <$> f x <*> f y
    LogOr x y -> LogOr <$> f x <*> f y
    LogImpl x y -> LogImpl <$> f x <*> f y
    LogEquiv x y -> LogEquiv <$> f x <*> f y

instance (Applicative f, Applicative g) => EvalOp f (PureEval g) LogicOp where
  evalOp f = \case
    LogLit b -> pure (pure b)
    LogNot x -> fmap not <$> f x
    LogAnd x y -> liftA2' f (&&) x y
    LogOr x y -> liftA2' f (||) x y
    LogImpl x y -> liftA2' f (S.==>) x y
    LogEquiv x y -> liftA2' f (S.<=>) x y

instance (Applicative f) => EvalOp f SBV LogicOp where
  evalOp f = \case
    LogLit b -> pure (S.fromBool b)
    LogNot x -> S.bnot <$> f x
    LogAnd x y -> liftA2 (S.&&&) (f x) (f y)
    LogOr x y -> liftA2 (S.|||) (f x) (f y)
    LogImpl x y -> liftA2 (S.==>) (f x) (f y)
    LogEquiv x y -> liftA2 (S.<=>) (f x) (f y)

instance HEq LogicOp where
  liftHEq _ _ (LogLit x) (LogLit y) = x == y
  liftHEq le _ (LogNot x) (LogNot y) = le svEq x y
  liftHEq le _ (LogAnd x1 x2) (LogAnd y1 y2) = le svEq x1 y1 && le svEq x2 y2
  liftHEq le _ (LogOr x1 x2) (LogOr y1 y2) = le svEq x1 y1 && le svEq x2 y2
  liftHEq le _ (LogImpl x1 x2) (LogImpl y1 y2) = le svEq x1 y1 && le svEq x2 y2
  liftHEq le _ (LogEquiv x1 x2) (LogEquiv y1 y2) = le svEq x1 y1 && le svEq x2 y2
  liftHEq _ _ _ _ = False

instance (Eq1 t) => Eq1 (LogicOp t) where liftEq = liftLiftEq

instance (Eq a, Eq1 t) => Eq (LogicOp t a) where (==) = eq1

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

liftA2' :: (Applicative f, Applicative g) => (a -> f (g b)) -> (b -> b -> c) -> a -> a -> f (g c)
liftA2' f g x y = getCompose (liftA2 g (Compose (f x)) (Compose (f y)))

svEq :: (Typeable a, Typeable b, Eq a) => a -> b -> Bool
svEq (x :: a) (y :: b)
  | Just Refl <- eqT :: Maybe (a :~: b) = x == y
  | otherwise = False
