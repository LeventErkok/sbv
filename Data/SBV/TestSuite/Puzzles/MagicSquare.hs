-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Puzzles.MagicSquare
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Puzzles.MagicSquare
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Puzzles.MagicSquare(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Puzzles.MagicSquare

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "magic 2" ~: assert . not =<< isSatisfiable (mkMagic 2)
 , "magic 3" ~: assert       =<< isSatisfiable (mkMagic 3)
 ]
 where mkMagic n = mkFreeVars (n*n) >>= output . isMagic . chunk n
