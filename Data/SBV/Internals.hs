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
    Result, runSymbolic
    -- * Other internal structures useful for low-level programming
  , SBV(..), HasSignAndSize(..), CW, mkConstCW, genFree, genFree_
  -- * Compilation to C
  , compileToC', compileToCLib', CgPgmBundle(..), CgPgmKind(..)
    -- * Integrating with the test framework
    -- $testFramework
  , module Data.SBV.Utils.SBVTest
  ) where

import Data.SBV.BitVectors.Data   (Result, runSymbolic, SBV(..), HasSignAndSize(..), CW, mkConstCW)
import Data.SBV.BitVectors.Model  (genFree, genFree_)
import Data.SBV.Compilers.C       (compileToC', compileToCLib')
import Data.SBV.Compilers.CodeGen (CgPgmBundle(..), CgPgmKind(..))
import Data.SBV.Utils.SBVTest

{- $compileC
Lower level access to program bundles, for further processing of program bundles.
-}

{- $testFramework
Functionality needed for extending SBV's internal test-suite. Only for developers of further libraries on
top of SBV.
-}
