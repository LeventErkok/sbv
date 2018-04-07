{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances       #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Core.Sequence
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Definition of symbolic sequences.
-----------------------------------------------------------------------------

module Data.SBV.Core.Sequence (Sequence(..)) where

import GHC.Exts

newtype Sequence a = Sequence { unSequence :: [a] }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, IsList)
