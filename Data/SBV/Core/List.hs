-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Core.Sequence
-- Copyright   :  (c) Joel Burget
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Definition of symbolic sequences.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances       #-}

module Data.SBV.Core.List (List(..)) where

import GHC.Exts

newtype List a = List { unList :: [a] }
     deriving (Eq, Ord, Show, Functor, Foldable, Traversable, IsList)
