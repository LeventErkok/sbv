-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Utils.ExtractIO
-- Copyright : (c) Brian Schroeder
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Helper typeclass for interoperation with APIs which take IO actions in
-- negative position.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Utils.ExtractIO where

import Control.Monad.Except      (ExceptT(ExceptT), runExceptT)
import Control.Monad.IO.Class    (MonadIO)
import Control.Monad.Trans.Maybe (MaybeT(MaybeT), runMaybeT)

import qualified Control.Monad.Writer.Lazy   as LW
import qualified Control.Monad.Writer.Strict as SW

-- | Monads which support 'IO' operations and can extract all 'IO' behavior for
-- interoperation with functions like 'Control.Concurrent.catches', which takes
-- an 'IO' action in negative position. This function can not be implemented
-- for transformers like @ReaderT r@ or @StateT s@, whose resultant 'IO'
-- actions are a function of some environment or state.
class MonadIO m => ExtractIO m where
    -- | Law: the @m a@ yielded by 'IO' is pure with respect to 'IO'.
    extractIO :: m a -> IO (m a)

-- | Trivial IO extraction for 'IO'.
instance ExtractIO IO where
    extractIO = pure

-- | IO extraction for 'MaybeT'.
instance ExtractIO m => ExtractIO (MaybeT m) where
    extractIO = fmap MaybeT . extractIO . runMaybeT

-- | IO extraction for 'ExceptT'.
instance ExtractIO m => ExtractIO (ExceptT e m) where
    extractIO = fmap ExceptT . extractIO . runExceptT

-- | IO extraction for lazy 'LW.WriterT'.
instance (Monoid w, ExtractIO m) => ExtractIO (LW.WriterT w m) where
    extractIO = fmap LW.WriterT . extractIO . LW.runWriterT

-- | IO extraction for strict 'SW.WriterT'.
instance (Monoid w, ExtractIO m) => ExtractIO (SW.WriterT w m) where
    extractIO = fmap SW.WriterT . extractIO . SW.runWriterT
