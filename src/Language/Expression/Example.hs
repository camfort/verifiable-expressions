{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}

{-|
"Language.Expression" provides a way of forming strongly types expression
languages from /operators/, via 'HFree'. This module is an explanation of how
that works, via a simple example.

This module is intended to be read via Haddock.
-}
module Language.Expression.Example where

import           Data.Functor.Identity (Identity (..))

import           Control.Monad.State

import           Data.Map              (Map)
import qualified Data.Map              as Map

import           Data.SBV              (EqSymbolic (..), OrdSymbolic (..),
                                        Predicate, SBV, Symbolic, isTheorem,
                                        ite, literal, symbolic)

import           Language.Expression

--------------------------------------------------------------------------------
-- * Operators

{-$
An /operator/ is a type constructor @op@ of kind @(* -> *) -> * -> *@. @op t
a@ should be seen as a way of combining @t@-objects which has a result type
@a@.

'SimpleOp' is an example of an operator type.
-}


{-|
An operator type has two arguments. @t@ is a type constructor used to refer to
expressions. @a@ is the semantic type of the expression formed by the operator.
-}
data SimpleOp t a where
  -- | Given two int expressions, we may add them. Notice how we refer to expressions
  -- recursively with the type constructor parameter @t@.
  Add :: t Integer -> t Integer -> SimpleOp t Integer

  -- | Given two int expressions, we may compare them for equality. Notice the
  -- types of the arguments to the operator do not appear in the result type at
  -- all.
  Equal :: t Integer -> t Integer -> SimpleOp t Bool

  -- | Operator constructors can have any number of arguments, and you can mix
  -- argument types.
  IfThenElse :: t Bool -> t Integer -> t Integer -> SimpleOp t Integer

  -- | An operator does not have to actually combine expressions. It may produce an
  -- expression from a basic value, i.e. a literal int. 'HFree' itself does
  -- /not/ provide literals so they must be encoded in operators.
  Literal :: Integer -> SimpleOp t Integer

-- ** Type Classes

{-$
Most useful operators are instances of 'HFunctor' (which provides 'hmap') and
'HTraversable' (which provides 'htraverse'). These are higher-ranked analogues
of 'Functor' and 'Traversable' from @base@. Compare the type signatures of
'fmap' and 'hmap':

@
'fmap' :: ('Functor' f) => (a -> b) -> f a -> f b
'hmap' :: ('HFunctor' h) => (forall b. s b -> t b) -> h s a -> h t a
@

'fmap' transforms the @*@-kinded type argument to @f@, while 'hmap' transforms
the @(* -> *)@-kinded type constructor argument to @h@.

So in order for an operator to have an instance of 'HFunctor', it must be
possible to swap out sub-expressions inside it. This is the case for our
'SimpleOp'.

'HTraversable' has a similar relationship with 'Traversable'. 'htraverse'
adds an applicative context to 'hmap'\'s transformations:

@
'traverse' :: ('Traversable' t, 'Applicative' f) => (a -> f b) -> t a -> f (t b)
'htraverse' :: ('HTraversable' h, 'Applicative' f) => (forall b. s b -> f (t b)) -> h s a -> f (h t a)
@

There is a default implementation of 'hmap' in terms of 'htraverse'.
-}

instance HFunctor SimpleOp
instance HTraversable SimpleOp where
  htraverse f = \case
    Add x y -> Add <$> f x <*> f y
    Equal x y -> Equal <$> f x <*> f y
    IfThenElse x y z -> IfThenElse <$> f x <*> f y <*> f z
    Literal x -> pure (Literal x)

--------------------------------------------------------------------------------
-- * Variables

{-$
As well as operators, expressions contain variables. Variables are also strongly
typed. A variable type @v@ has kind @* -> *@. The type parameter tells us the
type of the value that the variable is meant to represent.
-}


{-|
Notice that @a@ is a phantom type here (and it will be for most variable type
constructors). It is only used to restrict the type of values that are
representable by these variables. In this case, we only want to be able to store
integers so the only constructor has return type 'Integer'. It also contains a
'String' to be used as the variable name.
-}
data SimpleVar a where
  SimpleVar :: String -> SimpleVar Integer

--------------------------------------------------------------------------------
-- * Expressions

{-|
Now that we have defined our operators and variables, @'HFree' 'SimpleOp'
'SimpleVar' a@ is a syntax tree for a strongly typed expresson language.
-}
type SimpleExpr = HFree SimpleOp SimpleVar

--------------------------------------------------------------------------------
-- * A DSL

{-$
We can write simple wrapper functions to form a DSL for our expression language.
-}

{-|

@
var = 'hpure' . 'SimpleVar'
@

-}
var :: String -> SimpleExpr Integer
var = hpure . SimpleVar

{-|

@
x ^+ y = 'HWrap' ('Add' x y)
@

-}
(^+) :: SimpleExpr Integer -> SimpleExpr Integer -> SimpleExpr Integer
x ^+ y = HWrap (Add x y)

{-|

@
x ^== y = 'HWrap' ('Equal' x y)
@

-}
(^==) :: SimpleExpr Integer -> SimpleExpr Integer -> SimpleExpr Bool
x ^== y = HWrap (Equal x y)

{-|

@
ifThenElse x y z = 'HWrap' ('IfThenElse' x y z)
@

-}
ifThenElse :: SimpleExpr Bool -> SimpleExpr Integer -> SimpleExpr Integer -> SimpleExpr Integer
ifThenElse x y z = HWrap (IfThenElse x y z)

{-|

@
lit = 'HWrap' . 'Literal'
@

-}
lit :: Integer -> SimpleExpr Integer
lit = HWrap . Literal

--------------------------------------------------------------------------------
-- ** Example Expression

{-|
Here's an example of expression written using this DSL.

@
exampleExpr = 'ifThenElse' ('var' "x" '.==' 'lit' 10) ('var' "y") ('var' "y" '.+' 'lit' 5)
exampleExpr ~ if (x = 10) then y else y + 5
@
-}
exampleExpr :: SimpleExpr Integer
exampleExpr = ifThenElse (var "x" ^== lit 10) (var "y") (var "y" ^+ lit 5)

--------------------------------------------------------------------------------
-- * Expression Manipulation

{-$
If @op@ is an 'HFunctor', then @'HFree' op@ is an 'HMonad'. 'HMonad' defines
'hpure' (c.f. 'pure' or 'return'):

@
'hpure' :: ('HMonad' h) => t a -> h t a
'return' :: ('Monad' m) => a -> m a
@

and '^>>=' (c.f. '>>='):

@
('>>=') :: ('Monad' m) => m a -> (a -> m b) -> m b
('^>>=') :: ('HMonad' h) => h s a -> (forall b. s b -> h t b) -> h t a
@

In the case of @'HFree' op@, 'hpure' produces an expression containing a single
variable:

@
'hpure' :: v a -> 'HFree' op v a
@
-}

-- ** Substitution

{-$
'^>>=' substitutes variables inside expressions.
-}

{-|
'exampleExpr', with @x@ replaced by @z + 5@.

@
exampleExpr2 =
  exampleExpr '^>>=' \v@('SimpleVar' nm) ->
  if nm == "x" then 'var' "x" '^+' 'lit' 5 else 'hpure' v

exampleExpr2 ~ if ((z + 5) = 10) then y else y + 5
@

-}
exampleExpr2 :: SimpleExpr Integer
exampleExpr2 =
  exampleExpr ^>>= \v@(SimpleVar nm) ->
  if nm == "x" then var "z" ^+ lit 5 else hpure v

-- ** Traversal

{-$
When @op@ is an 'HTraversable', 'HFree' is also an 'HTraversable'. This can be
used, for example, to evaluate variables in an expression.
-}

{-|
This is a function that knows the value of variables with certain names. It will
return 'Nothing' if it doesn't know how to evaluate a particular variable.

@
evalXOrY ('SimpleVar' "x") = 'Just' 1
evalXOrY ('SimpleVar' "y") = 'Just' 2
evalXOrY _ = 'Nothing'
@

It might seem strange that we can return @'Just' ('Identity' 1)@ when the
function says it returns a @'Maybe' ('Identity' a)@ for polymorphic @a@. This
works because the constructor 'SimpleVar' must be 'Integer'-valued, so when we match
on it, GHC generates the constraint @a ~ 'Integer'@ and it will happily accept an
'Integer'.

Notice that, for @s ~ 'SimpleVar'@, @t ~ 'Identity'@ and @f ~ 'Maybe'@,

@
evalXOrY :: forall a. s a -> f (t a)
@

This means that we can traverse using this function:

>>> htraverse evalXOrY exampleExpr
htraverse evalXOrY exampleExpr :: Maybe (HFree SimpleOp Identity Integer)
htraverse evalXOrY exampleExpr ~ Just (if (1 = 10) then 2 else 2 + 5)

>>> htraverse evalXOrY exampleExpr2
htraverse evalXOrY exampleExpr2 :: Maybe (HFree SimpleOp Identity Integer)
htraverse evalXOrY exampleExpr2 ~ Nothing

There was a variable (@z@) that @evalXOrY@ didn't know how to evaluate, so the
traversal resulted in 'Nothing'!

-}
evalXOrY :: SimpleVar a -> Maybe (Identity a)
evalXOrY (SimpleVar "x") = Just (Identity 1)
evalXOrY (SimpleVar "y") = Just (Identity 2)
evalXOrY _               = Nothing

--------------------------------------------------------------------------------
-- * Evaluating Expressions

{-$
The 'HFoldableAt' type class provides the mechanism for evaluating operators,
and hence expressions.

@
'hfoldMap' :: ('HFoldableAt' k h) => (forall b. t b -> k b) -> h t b -> k b
@

Implemented in terms of this is

@
'hfoldTraverse'
  :: ('HFoldableAt' k h, 'HTraversable' h, 'Applicative' f)
  => (forall b. t b -> f (k b))
  -> h t a
  -> f (k a)
'hfoldTraverse' f = 'fmap' ('hfoldMap' 'id') . 'htraverse' f
@

This function will allow us to evaluate our expressions to ground values:

>>> hfoldTraverse evalXOrY exampleExpr
Just (Identity 7)

>>> hfoldTraverse evalXOrY exampleExpr2
Nothing

-}

instance HFoldableAt Identity SimpleOp where
  hfoldMap f s = case s of
    Add x y -> (+) <$> f x <*> f y
    Equal x y -> (==) <$> f x <*> f y
    IfThenElse x y z ->
      let ite' c a b = if c then a else b
      in ite' <$> f x <*> f y <*> f z
    Literal x -> pure x

--------------------------------------------------------------------------------
-- ** Evaluating Variables Symbolically

{-$
With the help of @sbv@, we can evaluate expressions symbolically in order to
prove things about them.
-}

{-|
Here's a function that converts variables in 'SimpleVar' to symbolic values. It
needs a @'Map' 'String' ('SBV' 'Integer')@ stateful environment in order to
remember variables that already have symbolic values, because 'SBV' will give
you different variables on two different calls of @'symbolic' x@ for the same
@x@.
-}
evalVarSymbolic :: SimpleVar a -> StateT (Map String (SBV Integer)) Symbolic (SBV a)
evalVarSymbolic (SimpleVar nm) = do
  existingSymbol <- gets (Map.lookup nm)
  case existingSymbol of
    Just x -> return x
    Nothing -> do
      newSymbol <- lift (symbolic nm)
      modify (Map.insert nm newSymbol)
      return newSymbol

--------------------------------------------------------------------------------
-- ** Evaluating Expressions Symbolically

{-$
We need an instance of @'HFoldableAt' 'SBV' 'SimpleOp'@ to do symbolic
evaluation, implemented like so:

@
instance 'HFoldableAt' 'SBV' 'SimpleOp' where
  'hfoldMap' = 'implHfoldMap' $ \s -> case s of
    'Add' x y          -> x '+' y
    'Equal' x y        -> x '.==' y
    'IfThenElse' x y z -> 'ite' x y z
    'Literal' x        -> 'literal' x
@
-}

instance HFoldableAt SBV SimpleOp where
  hfoldMap = implHfoldMap $ \s -> case s of
    Add x y          -> x + y
    Equal x y        -> x .== y
    IfThenElse x y z -> ite x y z
    Literal x        -> literal x

{-|
Now we can evaluate expressions symbolically and use @sbv@ to prove things about
them.

@
evalSimpleExprSymbolic = 'hfoldTraverse' 'evalVarSymbolic'
@
-}
evalSimpleExprSymbolic :: SimpleExpr a -> StateT (Map String (SBV Integer)) Symbolic (SBV a)
evalSimpleExprSymbolic = hfoldTraverse evalVarSymbolic

{-|

Let's ask @sbv@ to prove that our expression always returns a value no less than
the variable @y@.

@
examplePredicate = 'flip' 'evalStateT' 'mempty' $ do
  expr <- 'evalSimpleExprSymbolic' 'exampleExpr'
  y <- 'evalSimpleExprSymbolic' ('var' "y")
  'return' ('expr' '.>=' y)
@

>>> isTheorem examplePredicate
True

-}
examplePredicate :: Predicate
examplePredicate = flip evalStateT mempty $ do
  expr <- evalSimpleExprSymbolic exampleExpr
  y <- evalSimpleExprSymbolic (var "y")
  return (expr .>= y)
