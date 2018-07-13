-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Arrays.InitVals
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Testing arrays with initializers
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types #-}

module TestSuite.Arrays.InitVals(tests) where

import Utils.SBVTestFramework

readDef :: forall m. SymArray m => m Integer Integer -> Predicate
readDef proxy = do c <- free "c"
                   i <- free "i"
                   j <- free "j"
                   a <- newArray_ (Just c) `asTypeOf` return proxy

                   let a' = writeArray a j 32

                   return $ ite (i ./= j) (readArray a' i .== c)
                                          (readArray a' i .== 32)

readNoDef :: forall m. SymArray m => m Integer Integer -> Predicate
readNoDef proxy = do i <- free "i"
                     j <- free "j"

                     a <- newArray_ Nothing `asTypeOf` return proxy

                     return $ readArray a i .== j


tests :: TestTree
tests =
  testGroup "Arrays.InitVals"
    [ testCase "readDef_SArray"    $ assertIsThm (readDef (undefined :: SArray    Integer Integer))
    , testCase "readDef_SFunArray" $ assertIsThm (readDef (undefined :: SFunArray Integer Integer))

    , testCase "readDef_SArray"    $ assertIsSat (readNoDef (undefined :: SArray    Integer Integer))
    , testCase "readDef_SFunArray" $ assertIsSat (readNoDef (undefined :: SFunArray Integer Integer))
    ]
