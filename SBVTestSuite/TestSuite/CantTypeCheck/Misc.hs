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

{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- Defer type-errors is essential here!
{-# OPTIONS_GHC -Wall -Werror -Wno-orphans -Wno-deferred-type-errors -fdefer-type-errors #-}

module TestSuite.CantTypeCheck.Misc(tests) where

import Control.DeepSeq (NFData(..))
import Utils.SBVTestFramework

-- Only used safely!
import System.IO.Unsafe(unsafePerformIO)
instance NFData (IO Bool) where
  rnf iob = rnf (unsafePerformIO iob) `seq` ()

type Val = (Integer, Integer)

instance Num Val where
  (+)         = undefined
  (*)         = undefined
  (-)         = undefined
  signum      = undefined
  abs         = undefined
  fromInteger = undefined

tests :: TestTree
tests = testGroup "CantTypeCheck.Misc" [
           testCase "noTypeCheckBad01"  $ shouldNotTypeCheck $ isTheorem t1
         , testCase "noTypeCheckBad02"  $ shouldNotTypeCheck $ isTheorem t2
         , testCase "noTypeCheckBad03"  $ shouldNotTypeCheck   runSko
         , testCase "noTypeCheckBad04"  $ shouldNotTypeCheck   runNoNum
         , testCase "noTypeCheckGood01" $                      assertIsSat t1
         , testCase "noTypeCheckGood02" $                      assertIsSat t2

         -- Just so we got something other than our stuff..
         , testCase "noTypeCheck05"     $ shouldNotTypeCheck (1 :: String)
         ]
  where t1 :: SInteger -> ConstraintSet
        t1 x = do { constrain ( x .> (5::SInteger)) }

        t2 :: ConstraintSet
        t2 = pure ()

        -- shouldn't be able to skolemize like this
        sko :: Forall "y" Integer -> SInteger
        sko = skolemize fml
          where fml :: Exists "x" Integer -> Forall "y" Integer -> SInteger
                fml (Exists x) (Forall y) = x + y

        -- We have to reduce the above to a IO Bool so the rnf instance does the right thing!
        -- Oh the horrors of "deferring type errors"
        runSko :: IO Bool
        runSko = isSatisfiable $ sko (Forall (literal 3))

        -- can't add SBV Val
        noNumSBV :: SBV Val -> SBV Val -> SBV Val
        noNumSBV x y = x + y

        runNoNum :: IO Bool
        runNoNum = isSatisfiable noNumSBV
