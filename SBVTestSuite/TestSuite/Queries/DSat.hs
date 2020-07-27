-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.DSat
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing dsat value extraction
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Queries.DSat (tests)  where

import Data.SBV.Control

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Query.DSat"
    [ goldenCapturedIO "dsat01" testQuery
    ]

testQuery :: FilePath -> IO ()
testQuery rf = do r <- runSMTWith dReal{verbose=True, redirectVerbose=Just rf} fv
                  appendFile rf ("\n FINAL:" ++ show r ++ "\nDONE!\n")

fv :: Symbolic (Maybe String, [AlgReal], [RationalCV], [Integer], [Bool])
fv = do a0 <- sReal    "a0"
        i0 <- sInteger "i0"
        b0 <- sBool    "b0"

        constrain $ a0 .> 2
        constrain $ a0 .<= 5

        query $ do a1 :: SReal    <- freshVar "a1"
                   i1 :: SInteger <- freshVar "i1"
                   b1 :: SBool    <- freshVar "b1"

                   constrain $ a1 .> 3
                   constrain $ a1 .<= 12

                   cs <- checkSat

                   case cs of
                     DSat p -> do va0 <- getValue a0
                                  va1 <- getValue a1
                                  vi0 <- getValue i0
                                  vi1 <- getValue i1
                                  vb0 <- getValue b0
                                  vb1 <- getValue b1

                                  let rva0 = algRealToRational va0
                                      rva1 = algRealToRational va1

                                      check r = case r of
                                                  RatInterval lo hi -> if realPoint lo <= realPoint hi
                                                                       then r
                                                                       else error $ "Bounds violated for: " ++ show r
                                                  _                 -> r

                                  pure (p, [va0, va1], map check [rva0, rva1], [vi0, vi1], [vb0, vb1])

                     _   -> error "didn't expect non-DSat here!"
