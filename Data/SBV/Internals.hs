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
-- should not need to use this module.
---------------------------------------------------------------------------------

module Data.SBV.Internals (
    -- * Running symbolic programs /manually/
    Result, runSymbolic, SBV(..)
    -- * Integrating with the test framework
    -- $testFramework
  , module Data.SBV.Utils.SBVTest
  ) where

import Data.SBV.BitVectors.Data (Result, runSymbolic, SBV(..))
import Data.SBV.Utils.SBVTest

{- $testFramework
Functionality needed for extending SBV's internal test-suite. Only for developers of further libraries on
top of SBV.
-}
