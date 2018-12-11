-----------------------------------------------------------------------------
-- |
-- Module      :  Documentation.SBV.Examples.Queries.Transformer
-- Copyright   :  (c) Brian Schroeder
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- A demonstration of the use of the QueryT transformer for queries that can
-- "go wrong".
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Documentation.SBV.Examples.Queries.Transformer where

import Control.Monad.Except (ExceptT, MonadError, throwError)

import Data.SBV.Trans
--import Data.SBV.Trans.Control

newtype Alloc a = Alloc { runAlloc :: SymbolicT (ExceptT String IO) a }
    deriving (Functor, Applicative, Monad, MonadError String)

data Env = Env { envX :: SInteger
               , envY :: SInteger
               }
    deriving (Eq, Show)

alloc :: String -> Alloc SInteger
alloc "" = throwError "tried to allocate unnamed value"
alloc nm = Alloc $ free nm

allocEnv :: Alloc Env
allocEnv = do
    x <- alloc "x"
    y <- alloc "y"
    pure $ Env x y
