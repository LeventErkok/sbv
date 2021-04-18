-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Arrays.Caching
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test case for https://github.com/LeventErkok/sbv/issues/541
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Arrays.Caching (tests)  where

import Utils.SBVTestFramework

tests :: TestTree
tests = testGroup "Arrays.Caching" [
            goldenCapturedIO "array_caching_01" (run (test True))
          , goldenCapturedIO "array_caching_02" (run (test False))
          ]
   where run :: Symbolic SBool -> FilePath -> IO ()
         run tst goldFile = do r <- satWith defaultSMTCfg{verbose=True, redirectVerbose = Just goldFile} tst
                               appendFile goldFile ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")

test :: Bool -> Symbolic SBool
test swap = do
    arr :: SArray Integer Integer <- newArray "items" (Just 0)
    x   <- sInteger "x"

    let ys = writeArray arr 0 2

        idx = x + 1

        ys1 = writeArray ys 0   (readArray ys idx)
        ys2 = writeArray ys idx 1

        v = if swap
               then ite (x .== 0) (readArray ys1 0) (readArray ys2 0)
               else ite (x ./= 0) (readArray ys2 0) (readArray ys1 0)

    pure $ v .== 1
