-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.BitPrecise.BrokenSearch
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- The classic "binary-searches are broken" example:
--     <http://ai.googleblog.com/2006/06/extra-extra-read-all-about-it-nearly.html>
-----------------------------------------------------------------------------

module Documentation.SBV.Examples.BitPrecise.BrokenSearch where

import Data.SBV
import Data.SBV.Tools.Overflow

-- | Model the mid-point computation of the binary search, which is broken due to arithmetic overflow.
-- Note how we use the overflow checking variants of the arithmetic operators. We have:
--
-- >>> checkArithOverflow midPointBroken
-- Documentation/SBV/Examples/BitPrecise/BrokenSearch.hs:33:28:+!: SInt32 addition overflows: Violated. Model:
--   low  = 2147483583 :: Int32
--   high = 2147483647 :: Int32
--
-- Indeed:
--
-- >>> (2147483583 + 2147483647) `div` (2::Int32)
-- -33
--
-- giving us a negative mid-point value!
midPointBroken :: SInt32 -> SInt32 -> SInt32
midPointBroken low high = (low +! high) /! 2

-- | The correct version of how to compute the mid-point. As expected, this version doesn't have any
-- underflow or overflow issues:
--
-- >>> checkArithOverflow midPointFixed
-- No violations detected.
--
-- As expected, the value is computed correctly too:
--
-- >>> checkCorrectMidValue midPointFixed
-- Q.E.D.
midPointFixed :: SInt32 -> SInt32 -> SInt32
midPointFixed low high = low +! ((high -! low) /! 2)

-- | Show that the variant suggested by the blog post is good as well:
--
--       @mid = ((unsigned int)low + (unsigned int)high) >> 1;@
--
-- In this case the overflow is eliminated by doing the computation at a wider
-- range:
--
-- >>> checkArithOverflow midPointAlternative
-- No violations detected.
--
-- And the value computed is indeed correct:
--
-- >>> checkCorrectMidValue midPointAlternative
-- Q.E.D.
midPointAlternative :: SInt32 -> SInt32 -> SInt32
midPointAlternative low high = sFromIntegral ((low' +! high') `shiftR` 1)
  where low', high' :: SWord32
        low'  = sFromIntegralChecked low
        high' = sFromIntegralChecked high

-------------------------------------------------------------------------------------
-- * Helpers
-------------------------------------------------------------------------------------

-- | A helper predicate to check safety under the conditions that @low@ is at least 0
-- and @high@ is at least @low@.
checkArithOverflow :: (SInt32 -> SInt32 -> SInt32) -> IO ()
checkArithOverflow f = do sr <- safe $ do low   <- sInt32 "low"
                                          high <- sInt32 "high"

                                          constrain $ low .>= 0
                                          constrain $ low .<= high

                                          output $ f low high

                          case filter (not . isSafe) sr of
                                 [] -> putStrLn "No violations detected."
                                 xs -> mapM_ print xs

-- | Another helper to show that the result is actually the correct value, if it was done over
-- 64-bit integers, which is sufficiently large enough.
checkCorrectMidValue :: (SInt32 -> SInt32 -> SInt32) -> IO ThmResult
checkCorrectMidValue f = prove $ do low  <- sInt32 "low"
                                    high <- sInt32 "high"

                                    constrain $ low .>= 0
                                    constrain $ low .<= high

                                    let low', high' :: SInt64
                                        low'  = sFromIntegral low
                                        high' = sFromIntegral high
                                        mid'  = (low' + high') `sDiv` 2

                                        mid   = f low high

                                    return $ sFromIntegral mid .== mid'

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
