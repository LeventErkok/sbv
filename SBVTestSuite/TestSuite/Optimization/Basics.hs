-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Optimization.Basics
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for optimization routines
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Optimization.Basics(tests) where

import Utils.SBVTestFramework
import Data.SBV.Control

import Control.Monad

import qualified Control.Exception as C

-- Test suite
tests :: TestTree
tests =
  testGroup "Optimization.Basics" $
       [ goldenVsStringShow "optBasics1" (optimize Lexicographic optBasics1)
       , goldenVsStringShow "optBasics2" (optimize Lexicographic optBasics2)
       , goldenCapturedIO   "qOpt_1"     (qOpt False)
       , goldenCapturedIO   "qOpt_2"     (qOpt True)
       ]
    ++ [ goldenVsStringShow ("optBasicsRange_" ++ n) (optimize Lexicographic f)
       | (n, f) <- [ ("08_unsigned_max", sWord8  "x" >>= maximize "m")
                   , ("08_unsigned_min", sWord8  "x" >>= minimize "m")
                   , ("16_unsigned_max", sWord16 "x" >>= maximize "m")
                   , ("16_unsigned_min", sWord16 "x" >>= minimize "m")
                   , ("32_unsigned_max", sWord32 "x" >>= maximize "m")
                   , ("32_unsigned_min", sWord32 "x" >>= minimize "m")
                   , ("64_unsigned_max", sWord64 "x" >>= maximize "m")
                   , ("64_unsigned_min", sWord64 "x" >>= minimize "m")
                   , ("08_signed_max",   sInt8   "x" >>= maximize "m")
                   , ("08_signed_min",   sInt8   "x" >>= minimize "m")
                   , ("16_signed_max",   sInt16  "x" >>= maximize "m")
                   , ("16_signed_min",   sInt16  "x" >>= minimize "m")
                   , ("32_signed_max",   sInt32  "x" >>= maximize "m")
                   , ("32_signed_min",   sInt32  "x" >>= minimize "m")
                   , ("64_signed_max",   sInt64  "x" >>= maximize "m")
                   , ("64_signed_min",   sInt64  "x" >>= minimize "m")
                   ]
       ]

optBasics1 :: ConstraintSet
optBasics1 = do x <- sInteger "x"
                y <- sInteger "y"

                constrain $ x .< 2
                constrain $ y - x .< 1

                maximize "x_plus_y" $ x+y

optBasics2 :: ConstraintSet
optBasics2 = do x <- sInteger "x"
                y <- sInteger "y"

                constrain $ x .< 4
                constrain $ y - x .< 1
                constrain $ y .> 1

                minimize "x_plus_y" $ x+y

qOpt :: Bool -> FilePath -> IO ()
qOpt mb rf = testQuery $ do
                vs <- forM [1 .. 5] $ \i -> do x <- sInteger ("x" <> show (i::Int))
                                               constrain $ 1 .<= x
                                               when mb $ constrain $ x .< 10
                                               maximize ("goal" <> show i) x
                                               pure x
                query $ do cs <- checkSat
                           case cs of
                             Sat -> forM vs getValue
                             _   -> pure []
 where testQuery fv = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} fv
                         appendFile rf ("\n FINAL:" ++ show r ++ "\nDONE!\n")
                      `C.catch` (\(e :: C.SomeException) -> appendFile rf ("\nEXCEPTION CAUGHT:\n" ++ show e ++ "\n"))
