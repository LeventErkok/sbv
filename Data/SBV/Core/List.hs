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

module Data.SBV.Core.List (List(..)) where

-- Older versions of GHC (8.0.1, for instance) cannot derive the List instance; sigh.

#if MIN_VERSION_base(4,10,0)
import GHC.Exts(IsList(..))
#endif

newtype List a = List { unList :: [a] }
     deriving (Eq, Ord, Show, Functor, Foldable, Traversable

#if MIN_VERSION_base(4,10,0)
              , IsList
#endif
              )
