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
    Result, SBVRunMode(..), runSymbolic, runSymbolic'
    -- * Other internal structures useful for low-level programming
  , SBV(..), HasSignAndSize(..), CW, mkConstCW, genFinVar, genFinVar_
  -- * Compilation to C
  , compileToC', compileToCLib', CgPgmBundle(..), CgPgmKind(..)
    -- * Integrating with the test framework
  ) where

import Data.SBV.BitVectors.Data   (Result, SBVRunMode(..), runSymbolic, runSymbolic', SBV(..), HasSignAndSize(..), CW, mkConstCW)
import Data.SBV.BitVectors.Model  (genFinVar, genFinVar_)
import Data.SBV.Compilers.C       (compileToC', compileToCLib')
import Data.SBV.Compilers.CodeGen (CgPgmBundle(..), CgPgmKind(..))

{- $compileC
Lower level access to program bundles, for further processing of program bundles.
-}
