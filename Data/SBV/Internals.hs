---------------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Internals
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Low level functions to access the SBV infrastructure, for developers who
-- want to build further tools on top of SBV. End-users of the library
-- should not need to use this module
---------------------------------------------------------------------------------

module Data.SBV.Internals (
    Result, runSymbolic, SBV(..)
  , showsAs, ioShowsAs, mkTestSuite, SBVTestSuite(..), module Test.HUnit
  ) where

import Data.SBV.BitVectors.Data(Result, runSymbolic, SBV(..))
import Data.SBV.Utils.SBVTest
import Test.HUnit
