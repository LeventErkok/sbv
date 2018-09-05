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

{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies               #-}

module Data.SBV.Core.List (List(..)) where

import GHC.Exts(IsList(..))

-- | A wrapper of lists, solely for the purpose of type-disambiguation tagging.
newtype List a = List { unList :: [a] }
     deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

-- Older versions of GHC (8.0.1, for instance) cannot derive the List instance; sigh.
-- So we manually derive it here.
instance IsList (List a) where
   type Item (List a) = a
   fromList = List
   toList   = unList
