-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Uninterpreted.AUF
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.Uninterpreted.AUF
-----------------------------------------------------------------------------

module TestSuite.Uninterpreted.AUF where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Uninterpreted.AUF

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "auf-0" ~: assert =<< isThm (newArray "a" Nothing >>= \a -> free "x" >>= \x -> free "y" >>= \y -> free "i" >>= \i -> return (thm1 x y a i))
 , "auf-1" ~: assert =<< isThm (newArray "b" Nothing >>= \b -> free "x" >>= \x -> free "y" >>= \y                    -> return (thm2 x y b))
 , "auf-2" ~: pgm `goldCheck` "auf-1.gold"
 ]
 where pgm = runSymbolic (True, Nothing) $ do
                x <- free "x"
                y <- free "y"
                a <- newArray "a" Nothing
                i <- free "initVal"
                output $ thm1 x y a i
