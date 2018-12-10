-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Control.Mono
-- Copyright   :  (c) Brian Schroeder
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Helper typeclass for interoperation with APIs which take IO actions in
-- negative position.
-----------------------------------------------------------------------------

module Data.SBV.Utils.ExtractIO where

import Control.Monad.IO.Class (MonadIO)

-- | Monads which support 'IO' operations and can extract all 'IO' behavior for
-- interoperation with functions like 'Control.Concurrent.catches', which takes
-- an 'IO' action in negative position.
class MonadIO m => ExtractIO m where
  -- | Law: the @m a@ yielded by 'IO' is pure with respect to 'IO'.
  extractIO :: m a -> IO (m a)

instance ExtractIO IO where
  extractIO = pure
