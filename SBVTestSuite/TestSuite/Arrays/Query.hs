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
    [ goldenCapturedIO "queryArrays1" $ t q1
    , goldenCapturedIO "queryArrays2" $ t q2
    , goldenCapturedIO "queryArrays3" $ t q3
    ]
    where t tc goldFile = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just goldFile} tc
                             appendFile goldFile ("\n FINAL:" ++ show r ++ "\nDONE!\n")

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

q2 :: Symbolic Word8
q2 = do i <- sWord8 "i"

        setLogic QF_UFBV

        query $ do constrain $ i .== select [0 .. 255] 0 i
                   _ <- checkSat
                   getValue i

q3 :: Symbolic Word8
q3 = do i <- sWord8 "i"

        setLogic QF_UFBV

        query $ do constrain $ i .== select (replicate 256 i) 0 i
                   _ <- checkSat
                   getValue i
