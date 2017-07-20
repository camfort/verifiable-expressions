{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE TemplateHaskell    #-}


module Language.While.Syntax where

import           Control.Applicative (liftA2)
import           Data.Data

import           Data.Map            (Map)
import qualified Data.Map            as Map
import           Data.Set            (Set)
import qualified Data.Set            as Set

import           Control.Monad.State

import           Control.Lens
import           Data.Data.Lens
import           Data.Set.Lens


data Expr l
  = EAdd (Expr l) (Expr l)
  | EMul (Expr l) (Expr l)
  | ESub (Expr l) (Expr l)
  | EVar l
  | ELit Integer
  deriving (Data, Typeable, Functor, Foldable, Traversable)

instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = EVar
  EAdd e1 e2 >>= f = EAdd (e1 >>= f) (e2 >>= f)
  EMul e1 e2 >>= f = EMul (e1 >>= f) (e2 >>= f)
  ESub e1 e2 >>= f = ESub (e1 >>= f) (e2 >>= f)
  EVar x >>= f = f x
  ELit x >>= _ = ELit x


data Bexpr l
  = BLess (Expr l) (Expr l)
  | BLessEq (Expr l) (Expr l)
  | BEq (Expr l) (Expr l)
  | BAnd (Bexpr l) (Bexpr l)
  | BOr (Bexpr l) (Bexpr l)
  | BNot (Bexpr l)
  deriving (Data, Typeable, Functor, Foldable, Traversable)

bindBexpr :: (a -> Expr b) -> Bexpr a -> Bexpr b
bindBexpr f = \case
  BLess e1 e2 -> BLess (e1 >>= f) (e2 >>= f)
  BLessEq e1 e2 -> BLessEq (e1 >>= f) (e2 >>= f)
  BEq e1 e2 -> BEq (e1 >>= f) (e2 >>= f)
  BAnd b1 b2 -> BAnd (bindBexpr f b1) (bindBexpr f b2)
  BOr b1 b2 -> BOr (bindBexpr f b1) (bindBexpr f b2)
  BNot bexpr -> BNot (bindBexpr f bexpr)

data Command l a
  = CAnn a (Command l a)
  | CSeq (Command l a) (Command l a)
  | CSkip
  | CAssign l (Expr l)
  | CIf (Bexpr l) (Command l a) (Command l a)
  | CWhile (Bexpr l) (Command l a)
  deriving (Data, Typeable, Functor, Foldable, Traversable)


makePrisms ''Expr
makePrisms ''Bexpr
makePrisms ''Command


data StepResult a
  = Terminated
  | Failed
  | Progress a
  deriving (Functor)


evalExpr :: (Num n) => (l -> Maybe n) -> Expr l -> Maybe n
evalExpr env = \case
  EAdd e1 e2 -> liftA2 (+) (evalExpr env e1) (evalExpr env e2)
  EMul e1 e2 -> liftA2 (*) (evalExpr env e1) (evalExpr env e2)
  ESub e1 e2 -> liftA2 (-) (evalExpr env e1) (evalExpr env e2)
  EVar loc -> env loc
  ELit val -> Just (fromInteger val)


evalBexpr :: (Num n, Ord n) => (l -> Maybe n) -> Bexpr l -> Maybe Bool
evalBexpr env = \case
  BLess e1 e2 -> liftA2 (<) (evalExpr env e1) (evalExpr env e2)
  BLessEq e1 e2 -> liftA2 (<=) (evalExpr env e1) (evalExpr env e2)
  BEq e1 e2 -> liftA2 (==) (evalExpr env e1) (evalExpr env e2)
  BAnd b1 b2 -> liftA2 (&&) (evalBexpr env b1) (evalBexpr env b2)
  BOr b1 b2 -> liftA2 (||) (evalBexpr env b1) (evalBexpr env b2)
  BNot bexpr -> not <$> evalBexpr env bexpr


oneStep :: (Ord l, Num n, Ord n) => Command l a -> State (Map l n) (StepResult (Command l a))
oneStep = \case
  CAnn ann c -> fmap (CAnn ann) <$> oneStep c

  CSeq c1 c2 ->
    do s <- oneStep c1
       case s of
         Terminated -> return (Progress c2)
         Failed -> return Failed
         Progress c1' -> return (Progress (CSeq c1' c2))

  CSkip -> return Terminated

  CAssign loc expr ->
    do env <- get
       oldVal <- use (at loc)
       case oldVal of
         Just _ ->
           case evalExpr (`Map.lookup` env) expr of
             Just val ->
               do at loc .= Just val
                  return Terminated
             Nothing -> return Failed
         -- Can't assign a memory location that doesn't exist
         Nothing -> return Failed

  CIf cond c1 c2 ->
    do env <- get
       case evalBexpr (`Map.lookup` env) cond of
         Just True -> return (Progress c1)
         Just False -> return (Progress c2)
         _ -> return Failed

  CWhile cond body ->
    do env <- get
       case evalBexpr (`Map.lookup` env) cond of
         Just True -> return (Progress (CSeq body (CWhile cond body)))
         Just False -> return Terminated
         _ -> return Failed


runCommand :: (Ord l, Num n, Ord n) => Command l a -> State (Map l n) Bool
runCommand command =
  do s <- oneStep command
     case s of
       Terminated -> return True
       Failed -> return False
       Progress command' -> runCommand command'
