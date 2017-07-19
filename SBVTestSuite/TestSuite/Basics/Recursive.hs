-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Basics.Recursive
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Some recursive definitions.
-----------------------------------------------------------------------------

module TestSuite.Basics.Recursive(tests) where

import Utils.SBVTestFramework

-- This is recursive and suffers from the termination problem.
-- But we can still prove a few things about it!
mgcd :: SWord8 -> SWord8 -> SWord8
mgcd a b = ite (b .== 0) a (mgcd b (a `sMod` b))

-- Same construction, expressed in terms of the dynamic interface

-- Test suite
tests :: TestTree
tests = testGroup "Basics.Recursive"
   [ testCase "recursive1"    $ assertIsThm $ \x -> mgcd    0 x .== x
   , testCase "recursive2"    $ assertIsThm $ \x -> mgcd    x 0 .== x
   ]
