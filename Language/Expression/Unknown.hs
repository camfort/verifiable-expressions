{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}

module Language.Expression.Unknown where

import           Data.Data                   (Data, Typeable)
import           Data.SBV                    (HasKind, SymWord)

import           Language.Expression.Classes (SymValue)

--------------------------------------------------------------------------------
--  Unknown-typed variables
--------------------------------------------------------------------------------

data Unknown

-- GHC complains about deriving instances for an empty data type, unless we use
-- standalone deriving.

deriving instance Typeable Unknown
deriving instance Data Unknown
deriving instance Show Unknown
deriving instance Eq Unknown
deriving instance Ord Unknown
deriving instance Read Unknown

instance HasKind Unknown
instance SymWord Unknown

instance SymValue Unknown

fromUnknown :: Unknown -> a
fromUnknown _ = error "absurd case in 'fromUnknown'"
