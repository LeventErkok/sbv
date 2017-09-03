-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Arrays.Query
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for query mode arrays
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.Arrays.Query(tests) where

import Data.SBV.Control

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Arrays.Query"
    [ goldenCapturedIO "queryArrays1" $ \rf -> do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} q1
                                                  appendFile rf ("\n FINAL:" ++ show r ++ "\nDONE!\n")
    ]

q1 :: Symbolic (Word8, Word8, Int8)
q1 = do m  :: SArray Word8 Int8 <- newArray "a"

        a1 <- sWord8 "a1"
        a2 <- sWord8 "a2"

        constrain $ a1 ./= a2

        v1 <- sInt8 "v1"

        query $ do constrain $ v1 .== readArray (writeArray m a1 v1) a1
                   _ <- checkSat
                   va1 <- getValue a1
                   va2 <- getValue a2
                   vv1 <- getValue v1
                   return (va1, va2, vv1)
