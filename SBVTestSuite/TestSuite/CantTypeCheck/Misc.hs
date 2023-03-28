-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CantTypeCheck.Misc
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for things that should not type-check
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances #-}

-- Defer type-errors is essential here!
{-# OPTIONS_GHC -Wall -Werror -Wno-orphans -Wno-deferred-type-errors -fdefer-type-errors #-}

module TestSuite.CantTypeCheck.Misc(tests) where

import Control.DeepSeq (NFData(..))
import Utils.SBVTestFramework

-- Only used safely!
import System.IO.Unsafe(unsafePerformIO)
instance NFData (IO Bool) where
  rnf iob = rnf (unsafePerformIO iob) `seq` ()

tests :: TestTree
tests = testGroup "CantTypeCheck.Misc" [
           testCase "noTypeCheckBad01"  $ shouldNotTypeCheck $ isTheorem t1
         , testCase "noTypeCheckBad02"  $ shouldNotTypeCheck $ isTheorem t2
         , testCase "noTypeCheckGood01" $                      assertIsSat t1
         , testCase "noTypeCheckGood02" $                      assertIsSat t2

         -- Just so we got something other than our stuff..
         , testCase "noTypeCheck05"     $ shouldNotTypeCheck (1 :: String)
         ]
  where t1 :: SInteger -> Goal
        t1 x = do { constrain ( x .> (5::SInteger)) }

        t2 :: Goal
        t2 = pure ()
