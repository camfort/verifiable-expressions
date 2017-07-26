{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE NoMonomorphismRestriction       #-}

module Language.While.Hoare.General where

import           Data.Data

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.State

import           Data.Map                   (Map)
-- import qualified Data.Map                   as Map
import           Data.SBV                   hiding (( # ))

import           Language.While.Assertions
import           Language.While.Expressions


--------------------------------------------------------------------------------
--  Internal Types
--------------------------------------------------------------------------------

data VerifierSymbol
  = VSInteger SInteger
  | VSBool SBool
  | VSReal SReal

makePrisms ''VerifierSymbol

class Verifiable a where
  _Symbol :: Prism' VerifierSymbol (SBV a)

instance Verifiable Integer where
  _Symbol = _VSInteger

instance Verifiable Bool where
  _Symbol = _VSBool

instance Verifiable AlgReal where
  _Symbol = _VSReal

data Var a where
  Var :: (SymWord a, Verifiable a) => String -> Var a

data VerifierState expr =
  VerifierState
  { _varSymbols    :: Map String VerifierSymbol
  , _varConditions :: [expr Var Bool]
  }

makeLenses ''VerifierState

--------------------------------------------------------------------------------
--  Exposed Types
--------------------------------------------------------------------------------

data VerifierError (expr :: (* -> *) -> * -> *)
  = VEMismatchedSymbolType String
  deriving (Show, Eq, Ord, Data, Typeable)
  -- ^ The same variable was used for two different symbol types

data Verifier expr a =
  Verifier
  { getVerifier :: StateT (VerifierState expr) (ExceptT (VerifierError expr) Symbolic) a
  }
  deriving (Functor)

instance Applicative (Verifier expr) where
  pure = return
  (<*>) = ap

instance Monad (Verifier expr) where
  return = Verifier . return

  Verifier x >>= f = Verifier (x >>= getVerifier . f)

instance MonadIO (Verifier expr) where
  liftIO = Verifier . liftIO

-- -- | An annotated sequence. Consists of runs of assignments, with other commands
-- -- separated by annotations.
-- data AnnSeq expr c
--   = JustAssign [(v, e)]
--   -- ^ Just a series of assignments without annotations
--   | CmdAssign c [(v, e)]
--   -- ^ A command followed by a series of assignments
--   | Annotation (AnnSeq v e c) SBool (AnnSeq v e c)
--   -- ^ An initial sequence, followed by an annotation, then another sequence
--   deriving (Show)

--------------------------------------------------------------------------------
--  Exposed Functions
--------------------------------------------------------------------------------

checkCondition :: (Substitutive expr) => PropOn (expr Var) Bool -> Verifier expr Bool
checkCondition = undefined

-- verifySequence :: (Variable v) =>  (c -> Verifier v ()) -> AnnSeq v e c -> Verifier v ()
-- verifySequence verifyCommand seq = undefined

-- addCondition :: SBool -> Verifier v ()
-- addCondition cond = Verifier (varConditions %= (cond :))

--------------------------------------------------------------------------------
--  Internal Functions
--------------------------------------------------------------------------------

propToSBV :: (Substitutive expr, HoistOp SBV expr) => PropOn (expr Var) Bool -> Verifier expr SBool
propToSBV prop = do
  propWithSymbols <- traverseOp (traverseOp symbolVar) prop

  let evalExpr' = runIdentity . evalOp . hoistOp pure
      result = evalExpr' (mapOp evalExpr' propWithSymbols)

  return result

liftSymbolic :: Symbolic a -> Verifier v a
liftSymbolic = Verifier . lift . lift

symbolVar :: Var a -> Verifier expr (SBV a)
symbolVar (Var varName) = do
  storedSymbol <- Verifier $ use (varSymbols . at varName)

  case storedSymbol of
    Just s -> maybe (Verifier $ throwError (VEMismatchedSymbolType varName))
              return
              (s ^? _Symbol)
    Nothing -> do
      newSymbol <- liftSymbolic (symbolic varName)
      Verifier $ varSymbols . at varName .= Just (_Symbol # newSymbol)
      return newSymbol
