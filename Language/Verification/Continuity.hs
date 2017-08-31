{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Language.While.Continuity where

import           Data.SBV

import           Data.Set              (Set)
import qualified Data.Set              as Set

import           Language.While.Hoare
import           Language.While.Syntax

import Language.Expression


  

-- data OpSpec =
--   OpSpec
--   { _osPrecondition :: Prop Int
--   , _osOpContinuity :: Set Int
--   }
--   deriving (Show)


-- exprOpSpecs :: ExprOp a -> [OpSpec]
-- exprOpSpecs = \case
--   OAdd _ _ -> [OpSpec (PLit True) (Set.fromList [0, 1])]
--   OMul _ _ -> [OpSpec (PLit True) (Set.fromList [0, 1])]
--   OSub _ _ -> [OpSpec (PLit True) (Set.fromList [0, 1])]


-- -- | @'exprContinuous' allVars prop inputs expr@ judges whether @expr@ is
-- -- continuous with respect to the given input variables, whenever the current
-- -- program state is one in which @prop@ is true. @allVars@ constrains the
-- -- variables in the program.
-- exprContinuous :: (Ord l) => Set l -> WhileProp l -> Set l -> Expr l -> Bool
-- exprContinuous = undefined


-- newtype SetVar = SetVar Int


-- data SetExpr l v
--   = SVar v
--   | SLit (Set l)
--   | SUnion (SetExpr l v) (SetExpr l v)
--   | SDiff


-- data SetProp l v
--   = Subset (SetExpr l v) (SetExpr l v)


-- class Monad m => MonadProveCont l m | m -> l where
--   -- Fresh variables
--   -- Adding proof obligations
--   -- Discharging some of the existing proof obligations
--   -- Querying state

-- -- | @'findContinuity' prop inputs command@ yields the largest set of output
-- -- variables such that the outputs vary continuously in the inputs when
-- -- @command@ from a state which satisfies @prop@.
-- findContinuity :: (MonadProveCont l m) => Prop l -> Set l -> Command l a -> m (Set l)
-- findContinuity prop inputs command = undefined

-- -- | @'continuityVcs' subspace inputs outputs command@ computes the verification
-- -- conditions for each of the variables in @outputs@ to vary continuously with
-- -- respect to each of the variables in @inputs@, after running @command@.
-- continuityVcs :: Prop l -> [l] -> [l] -> Command l a -> SBool
-- continuityVcs prop inputs outputs = undefined
