{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE TemplateHaskell    #-}


module Language.While.Syntax where

import           Data.Data
import           Data.String         (IsString (..))

import           Data.Map            (Map)
import qualified Data.Map            as Map

import           Control.Monad.State

import           Control.Lens        hiding (op)

--------------------------------------------------------------------------------
--  Arithmetic expressions
--------------------------------------------------------------------------------

data ExprOp a = OAdd a a | OMul a a | OSub a a
  deriving (Show, Data, Typeable, Functor, Foldable, Traversable)

evalExprOp :: (Num n) => ExprOp n -> n
evalExprOp = \case
  OAdd x y -> x + y
  OMul x y -> x * y
  OSub x y -> x - y

data Expr l
  = EOp (ExprOp (Expr l))
  | EVar l
  | ELit Integer
  deriving (Show, Data, Typeable, Functor, Foldable, Traversable)


pattern EAdd :: Expr t -> Expr t -> Expr t
pattern EAdd a b = EOp (OAdd a b)

pattern EMul :: Expr t -> Expr t -> Expr t
pattern EMul a b = EOp (OMul a b)

pattern ESub :: Expr t -> Expr t -> Expr t
pattern ESub a b = EOp (OSub a b)


instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = EVar
  EOp op >>= f = EOp (fmap (>>= f) op)
  EVar x >>= f = f x
  ELit x >>= _ = ELit x

instance Num (Expr l) where
  fromInteger = ELit

  (+) = EAdd
  (*) = EMul
  (-) = ESub
  abs = error "can't take abs of expressions"
  signum = error "can't take signum of expressions"

instance IsString s => IsString (Expr s) where
  fromString = EVar . fromString

--------------------------------------------------------------------------------
--  Boolean expressions
--------------------------------------------------------------------------------

data ArithOp a
  = OLess a a
  | OLessEq a a
  | OEq a a
  deriving (Show, Data, Typeable, Functor, Foldable, Traversable)


data BoolOp a
  = OAnd a a
  | OOr a a
  | ONot a
  deriving (Show, Data, Typeable, Functor, Foldable, Traversable)


evalArithOp :: (Ord n) => ArithOp n -> Bool
evalArithOp = \case
  OLess a b -> a < b
  OLessEq a b -> a <= b
  OEq a b -> a == b


evalBoolOp :: BoolOp Bool -> Bool
evalBoolOp = \case
  OAnd a b -> a && b
  OOr a b -> a || b
  ONot a -> not a


data Bexpr l
  = BArithOp (ArithOp (Expr l))
  | BBoolOp (BoolOp (Bexpr l))
  deriving (Show, Data, Typeable, Functor, Foldable, Traversable)


pattern BLess :: Expr t -> Expr t -> Bexpr t
pattern BLess a b = BArithOp (OLess a b)

pattern BLessEq :: Expr t -> Expr t -> Bexpr t
pattern BLessEq a b = BArithOp (OLessEq a b)

pattern BEq :: Expr t -> Expr t -> Bexpr t
pattern BEq a b = BArithOp (OEq a b)


pattern BAnd :: Bexpr t -> Bexpr t -> Bexpr t
pattern BAnd a b = BBoolOp (OAnd a b)

pattern BOr :: Bexpr t -> Bexpr t -> Bexpr t
pattern BOr a b = BBoolOp (OOr a b)

pattern BNot :: Bexpr t -> Bexpr t
pattern BNot a = BBoolOp (ONot a)


bindBexpr :: (a -> Expr b) -> Bexpr a -> Bexpr b
bindBexpr f = \case
  BArithOp op -> BArithOp (fmap (>>= f) op)
  BBoolOp op -> BBoolOp (fmap (bindBexpr f) op)


data Command l a
  = CAnn a (Command l a)
  | CSeq (Command l a) (Command l a)
  | CSkip
  | CAssign l (Expr l)
  | CIf (Bexpr l) (Command l a) (Command l a)
  | CWhile (Bexpr l) (Command l a)
  deriving (Show, Data, Typeable, Functor, Foldable, Traversable)


makePrisms ''Expr
makePrisms ''Bexpr
makePrisms ''Command


data StepResult a
  = Terminated
  | Failed
  | Progress a
  deriving (Functor)


evalExpr :: (Num n, Applicative f) => (l -> f n) -> Expr l -> f n
evalExpr env = \case
  EOp op -> evalExprOp <$> traverse (evalExpr env) op
  EVar loc -> env loc
  ELit val -> pure (fromInteger val)


evalBexprGeneral
  :: (Num n, Applicative f)
  => (ArithOp n -> bool)
  -> (BoolOp bool -> bool)
  -> (l -> f n)
  -> Bexpr l
  -> f bool
evalBexprGeneral evalArith evalBool env = \case
  BArithOp op -> evalArith <$> traverse (evalExpr env) op
  BBoolOp op -> evalBool <$> traverse (evalBexprGeneral evalArith evalBool env) op


evalBexpr :: (Num n, Ord n, Applicative f) => (l -> f n) -> Bexpr l -> f Bool
evalBexpr = evalBexprGeneral evalArithOp evalBoolOp


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
       if Map.member loc env then
         case evalExpr (`Map.lookup` env) expr of
           Just val ->
             do at loc .= Just val
                return Terminated
           Nothing -> return Failed
         -- Can't assign a memory location that doesn't exist
         else return Failed

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
