{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE PatternSynonyms    #-}


module Language.While.Syntax where

import           Data.String         (IsString (..))

import           Control.Applicative (liftA2)
import Data.SBV

-- These imports are used for evaluating commands
-- import           Data.Map            (Map)
-- import qualified Data.Map            as Map
-- import           Control.Monad.State

import Language.Expression
import Language.Expression.Pretty

data WhileOp t a where
  OpAdd, OpSub, OpMul :: t Integer -> t Integer -> WhileOp t Integer
  OpEq, OpLT, OpLE, OpGT, OpGE :: t Integer -> t Integer -> WhileOp t Bool
  OpNot :: t Bool -> WhileOp t Bool
  OpAnd, OpOr :: t Bool -> t Bool -> WhileOp t Bool
  OpLitInteger :: Integer -> WhileOp t Integer
  OpLitBool :: Bool -> WhileOp t Bool

instance Operator WhileOp where
  htraverseOp f = \case
    OpAdd x y -> OpAdd <$> f x <*> f y
    OpSub x y -> OpSub <$> f x <*> f y
    OpMul x y -> OpMul <$> f x <*> f y
    OpEq x y -> OpEq <$> f x <*> f y
    OpLT x y -> OpLT <$> f x <*> f y
    OpLE x y -> OpLE <$> f x <*> f y
    OpGT x y -> OpGT <$> f x <*> f y
    OpGE x y -> OpGE <$> f x <*> f y
    OpNot x -> OpNot <$> f x
    OpAnd x y -> OpAnd <$> f x <*> f y
    OpOr x y -> OpOr <$> f x <*> f y
    OpLitInteger x -> pure (OpLitInteger x)
    OpLitBool x -> pure (OpLitBool x)

instance HEq WhileOp where
  liftHEq le _ (OpAdd x1 y1) (OpAdd x2 y2) = le (==) x1 x2 && le (==) y1 y2
  liftHEq le _ (OpSub x1 y1) (OpSub x2 y2) = le (==) x1 x2 && le (==) y1 y2
  liftHEq le _ (OpMul x1 y1) (OpMul x2 y2) = le (==) x1 x2 && le (==) y1 y2
  liftHEq le _ (OpEq x1 y1) (OpEq x2 y2) = le (==) x1 x2 && le (==) y1 y2
  liftHEq le _ (OpLT x1 y1) (OpLT x2 y2) = le (==) x1 x2 && le (==) y1 y2
  liftHEq le _ (OpLE x1 y1) (OpLE x2 y2) = le (==) x1 x2 && le (==) y1 y2
  liftHEq le _ (OpGT x1 y1) (OpGT x2 y2) = le (==) x1 x2 && le (==) y1 y2
  liftHEq le _ (OpGE x1 y1) (OpGE x2 y2) = le (==) x1 x2 && le (==) y1 y2
  liftHEq le _ (OpAnd x1 y1) (OpAnd x2 y2) = le (==) x1 x2 && le (==) y1 y2
  liftHEq le _ (OpOr x1 y1) (OpOr x2 y2) = le (==) x1 x2 && le (==) y1 y2
  liftHEq le _ (OpNot x) (OpNot y) = le (==) x y
  liftHEq _ _ (OpLitInteger x) (OpLitInteger y) = x == y
  liftHEq _ _ (OpLitBool x) (OpLitBool y) = x == y
  liftHEq _ _ _ _ = False

instance Pretty2 WhileOp where
  prettys2Prec p = \case
    OpAdd x y ->
      showParen (p > 5) $ prettys1Prec 6 x . showString " + " . prettys1Prec 6 y
    OpSub x y ->
      showParen (p > 5) $ prettys1Prec 6 x . showString " - " . prettys1Prec 6 y
    OpMul x y ->
      showParen (p > 6) $ prettys1Prec 7 x . showString " * " . prettys1Prec 7 y

    OpEq x y ->
      showParen (p > 4) $ prettys1Prec 5 x . showString " = " . prettys1Prec 5 y

    OpLT x y ->
      showParen (p > 4) $ prettys1Prec 5 x . showString " < " . prettys1Prec 5 y
    OpLE x y ->
      showParen (p > 4) $ prettys1Prec 5 x . showString " <= " . prettys1Prec 5 y
    OpGT x y ->
      showParen (p > 4) $ prettys1Prec 5 x . showString " > " . prettys1Prec 5 y
    OpGE x y ->
      showParen (p > 4) $ prettys1Prec 5 x . showString " >= " . prettys1Prec 5 y

    OpNot x -> showParen (p > 8) $ showString "! " . prettys1Prec 9 x
    OpAnd x y ->
      showParen (p > 3) $ prettys1Prec 4 x . showString " && " . prettys1Prec 4 y
    OpOr x y ->
      showParen (p > 2) $ prettys1Prec 3 x . showString " || " . prettys1Prec 3 y

    OpLitInteger x -> shows x
    OpLitBool x -> shows x

instance (Applicative f) => EvalOp f SBV WhileOp where
  evalOp f = \case
    OpAdd x y -> liftA2 (+) (f x) (f y)
    OpSub x y -> liftA2 (-) (f x) (f y)
    OpMul x y -> liftA2 (*) (f x) (f y)

    OpEq x y -> liftA2 (.==) (f x) (f y)
    OpLT x y -> liftA2 (.<) (f x) (f y)
    OpLE x y -> liftA2 (.<=) (f x) (f y)
    OpGT x y -> liftA2 (.>) (f x) (f y)
    OpGE x y -> liftA2 (.>=) (f x) (f y)

    OpAnd x y -> liftA2 (&&&) (f x) (f y)
    OpOr x y -> liftA2 (|||) (f x) (f y)
    OpNot x -> bnot <$> f x

    OpLitInteger x -> pure (fromInteger x)
    OpLitBool x -> pure (fromBool x)

data WhileVar l a where
  WhileVar :: l -> WhileVar l Integer

instance Pretty l => Pretty1 (WhileVar l) where
  pretty1 (WhileVar l) = pretty l

type WhileExpr l = Expr WhileOp (WhileVar l)

(...) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(f ... g) x y = f (g x y)

instance Num (WhileExpr l Integer) where
  fromInteger = EOp . OpLitInteger . fromInteger

  (+) = EOp ... OpAdd
  (*) = EOp ... OpMul
  (-) = EOp ... OpSub
  abs = error "can't take abs of expressions"
  signum = error "can't take signum of expressions"

instance IsString s => IsString (WhileExpr s Integer) where
  fromString = EVar . WhileVar . fromString

pattern BLess :: WhileExpr l Integer -> WhileExpr l Integer -> WhileExpr l Bool
pattern BLess a b = EOp (OpLT a b)

pattern BLessEq :: WhileExpr l Integer -> WhileExpr l Integer -> WhileExpr l Bool
pattern BLessEq a b = EOp (OpLE a b)

pattern BEq :: WhileExpr l Integer -> WhileExpr l Integer -> WhileExpr l Bool
pattern BEq a b = EOp (OpEq a b)


pattern BAnd :: WhileExpr l Bool -> WhileExpr l Bool -> WhileExpr l Bool
pattern BAnd a b = EOp (OpAnd a b)

pattern BOr :: WhileExpr l Bool -> WhileExpr l Bool -> WhileExpr l Bool
pattern BOr a b = EOp (OpOr a b)

pattern BNot :: WhileExpr l Bool -> WhileExpr l Bool
pattern BNot a = EOp (OpNot a)


data Command l a
  = CAnn a (Command l a)
  | CSeq (Command l a) (Command l a)
  | CSkip
  | CAssign l (WhileExpr l Integer)
  | CIf (WhileExpr l Bool) (Command l a) (Command l a)
  | CWhile (WhileExpr l Bool) (Command l a)

instance (Pretty l, Pretty a) => Pretty (Command l a) where
  prettysPrec p = \case
    CAnn ann c -> showParen (p > 10) $ showString "{ " . prettys ann . showString " }\n" . prettys c
    CSeq c1 c2 -> showParen (p > 10) $ prettys c1 . showString ";\n" . prettys c2
    CSkip -> showString "()"
    CAssign v e -> showParen (p > 10) $ prettys v . showString " := " . prettys e
    CIf cond c1 c2 -> showParen (p > 10) $ showString "if " . prettysPrec 11 cond . showString " then\n" . prettysPrec 11 c1 . showString "\nelse\n" . prettysPrec 11 c2
    CWhile cond body -> showParen (p > 10) $ showString "while " . prettysPrec 11 cond . showString " do\n" . prettysPrec 11 body

-- data StepResult a
--   = Terminated
--   | Failed
--   | Progress a
--   deriving (Functor)


-- oneStep :: (Ord l, Num n, Ord n) => Command l a -> State (Map l n) (StepResult (Command l a))
-- oneStep = \case
--   CAnn ann c -> fmap (CAnn ann) <$> oneStep c

--   CSeq c1 c2 ->
--     do s <- oneStep c1
--        case s of
--          Terminated -> return (Progress c2)
--          Failed -> return Failed
--          Progress c1' -> return (Progress (CSeq c1' c2))

--   CSkip -> return Terminated

--   CAssign loc expr ->
--     do env <- get
--        if Map.member loc env then
--          case evalExpr (`Map.lookup` env) expr of
--            Just val ->
--              do at loc .= Just val
--                 return Terminated
--            Nothing -> return Failed
--          -- Can't assign a memory location that doesn't exist
--          else return Failed

--   CIf cond c1 c2 ->
--     do env <- get
--        case evalBexpr (`Map.lookup` env) cond of
--          Just True -> return (Progress c1)
--          Just False -> return (Progress c2)
--          _ -> return Failed

--   CWhile cond body ->
--     do env <- get
--        case evalBexpr (`Map.lookup` env) cond of
--          Just True -> return (Progress (CSeq body (CWhile cond body)))
--          Just False -> return Terminated
--          _ -> return Failed


-- runCommand :: (Ord l, Num n, Ord n) => Command l a -> State (Map l n) Bool
-- runCommand command =
--   do s <- oneStep command
--      case s of
--        Terminated -> return True
--        Failed -> return False
--        Progress command' -> runCommand command'
