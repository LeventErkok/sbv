-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Arrays.InitVals
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing arrays with initializers
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Arrays.InitVals(tests) where

import Data.SBV
import Utils.SBVTestFramework

readDef :: Predicate
readDef = do c :: SInteger <- free "c"
             i :: SInteger <- free "i"
             j <- free "j"
             let a = lambdaArray (const c)

             let a' = writeArray a j 32

             return $ ite (i ./= j) (readArray a' i .== c)
                                    (readArray a' i .== 32)

readNoDef :: Predicate
readNoDef = do i :: SInteger <- free "i"
               j :: SInteger <- free "j"

               a <- sArray_

               return $ readArray a i .== j

constArr :: Predicate
constArr = do i :: SInteger <- sInteger "i"
              j :: SInteger <- sInteger "j"

              constrain $ i .< j
              constrain $ i `sElem` [1, 2, 3, 75]
              pure $ readArray myArray i .== readArray myArray j
  where myArray = listArray [(1, 12), (2, 5) , (3, 6), (75, 5)] (7 :: Integer)

constArr2 :: Predicate
constArr2 = do i :: SInteger <- sInteger "i"
               j :: SInteger <- sInteger "j"

               constrain $ i .< j
               constrain $ i `sElem` [1, 2, 3, 75]
               pure $ readArray myArray i .== readArray myArray j
  where myArray = listArray [(1, 12), (2, 5) , (3, 6), (75, 5)] (2 :: Integer)

tests :: TestTree
tests = testGroup "Arrays" [
    testGroup "Arrays.InitVals"
      [ testCase "readDef_SArray"           $ assertIsThm readDef
      , testCase "readDef2_SArray2"         $ assertIsSat readNoDef
      , goldenCapturedIO "constArr_SArray"  $ t satWith constArr
      , goldenCapturedIO "constArr2_SArray" $ t satWith constArr2
      ]
  , testGroup "Arrays.Misc"
      [ goldenCapturedIO "array_misc_1"  $ t proveWith $ \i -> readArray (listArray [(True,1),(False,0)] 3) i .<= (1::SInteger)

      , goldenCapturedIO "array_misc_2"  $ t satWith   $ \(x :: SArray Integer Integer) i1 i2 i3 ->
                                                                 readArray x i1 .== 4 .&& readArray x i2 .== 5 .&& readArray x i3 .== 12

      , goldenCapturedIO "array_misc_3"  $ t proveWith $      write (empty False) [(True, True), (False, False)]
                                                          .== write (empty True)  [(True, True), (False, False)]

      , testCase         "array_misc_4"  $                   (write (empty False) [(True, True), (False, False)]
                                                          .== write (empty True)  [(True, True), (False, False)]) `showsAs` "True"

      -- Interestingly, z3 says UNKNOWN if the logic below isn't set to ALL.
      , goldenCapturedIO "array_misc_5"  $ t proveWith $ do setLogic Logic_ALL
                                                            pure (    write (empty 0) [(i, i) | i <- [0 .. (3 :: WordN 2)]]
                                                                  .== write (empty 1) [(i, i) | i <- [0 .. (3 :: WordN 2)]]) :: Symbolic SBool

      , testCase         "array_misc_6"  $                   (write (empty 0) [(i, i) | i <- [0 .. (3 :: WordN 2)]]
                                                          .== write (empty 1) [(i, i) | i <- [0 .. (3 :: WordN 2)]]) `showsAs` "<symbolic> :: SBool"

      , goldenCapturedIO "array_misc_7"  $ t proveWith $      write (empty 0) [(i, i) | i <- [0 .. (3 :: WordN 2)]]
                                                          .== write (empty 0) [(i, i) | i <- [0 .. (3 :: WordN 2)]]

      , testCase         "array_misc_8"  $                   (write (empty 0) [(i, i) | i <- [0 .. (3 :: WordN 2)]]
                                                          .== write (empty 0) [(i, i) | i <- [0 .. (3 :: WordN 2)]]) `showsAs` "True"

      , goldenCapturedIO "array_misc_9"   $ t proveWith $     write (empty 0) [(i, i+1) | i <- [0 .. (3 :: WordN 2)]]
                                                          .== write (empty 0) [(i, i)   | i <- [0 .. (3 :: WordN 2)]]

      , testCase         "array_misc_10" $                   (write (empty 0) [(i, i+1) | i <- [0 .. (3 :: WordN 2)]]
                                                          .== write (empty 0) [(i, i  ) | i <- [0 .. (3 :: WordN 2)]]) `showsAs` "False"

      , goldenCapturedIO "array_misc_11" $ t satWith $ \(a :: SArray (Integer, Integer) Integer) -> readArray a (literal (1, 2)) .== 3
      , goldenCapturedIO "array_misc_12" $ t satWith $ \(a :: SArray Integer (Integer, Integer)) -> readArray a 3 .== literal (1, 2)

      , goldenCapturedIO "array_misc_13" $ t satWith $ \(a :: SArray (Integer, Integer) (Integer, Integer)) -> readArray a (literal (1, 2)) .== literal (1, 2)
      , goldenCapturedIO "array_misc_14" $ t satWith $ \(a :: SArray Integer Float)   -> fpIsNaN (readArray a 2)
      , goldenCapturedIO "array_misc_15" $ t satWith $ \(a :: SArray Float   Integer) -> readArray a (0/0) .== 3

      , goldenCapturedIO "array_misc_16" $ t satWith (.== readArray (listArray [(0, 12)] 3 :: SArray Float                Integer) 0)
      , goldenCapturedIO "array_misc_17" $ t satWith (.== readArray (listArray [(0, 12)] 3 :: SArray Double               Integer) 0)
      , goldenCapturedIO "array_misc_18" $ t satWith (.== readArray (listArray [(0, 12)] 3 :: SArray (FloatingPoint 10 4) Integer) (0 :: SFloatingPoint 10 4))

      , goldenCapturedIO "array_misc_19" $ t satWith (.== readArray (listArray [(0, 12)] 3 :: SArray Float                Integer) (-0))
      , goldenCapturedIO "array_misc_20" $ t satWith (.== readArray (listArray [(0, 12)] 3 :: SArray Double               Integer) (-0))
      , goldenCapturedIO "array_misc_21" $ t satWith (.== readArray (listArray [(0, 12)] 3 :: SArray (FloatingPoint 10 4) Integer) (-(0 :: SFloatingPoint 10 4)))

      , goldenCapturedIO "array_misc_22" $ t satWith (.== readArray (listArray [(0/0, 12)] 3 :: SArray Float                Integer) (0/0))
      , goldenCapturedIO "array_misc_23" $ t satWith (.== readArray (listArray [(0/0, 12)] 3 :: SArray Double               Integer) (0/0))
      , goldenCapturedIO "array_misc_24" $ t satWith (.== readArray (listArray [(0/0, 12)] 3 :: SArray (FloatingPoint 10 4) Integer) (0/0))

      , goldenCapturedIO "array_misc_25" $ t satWith (.== readArray (listArray [(1/0, 12)] 3 :: SArray Float                Integer) (1/0))
      , goldenCapturedIO "array_misc_26" $ t satWith (.== readArray (listArray [(1/0, 12)] 3 :: SArray Double               Integer) (1/0))
      , goldenCapturedIO "array_misc_27" $ t satWith (.== readArray (listArray [(1/0, 12)] 3 :: SArray (FloatingPoint 10 4) Integer) (1/0))

      , goldenCapturedIO "array_misc_28" $ t satWith (.== readArray (listArray [(1/0, 12)] 3 :: SArray Float                Integer) (-(1/0)))
      , goldenCapturedIO "array_misc_29" $ t satWith (.== readArray (listArray [(1/0, 12)] 3 :: SArray Double               Integer) (-(1/0)))
      , goldenCapturedIO "array_misc_30" $ t satWith (.== readArray (listArray [(1/0, 12)] 3 :: SArray (FloatingPoint 10 4) Integer) (-(1/0)))

      , goldenCapturedIO "array_misc_31" $ t proveWith (listArray [(1, 2), (3, 4)] 5 .== listArray [(3 :: Integer, 4), (1, 2)] (5 :: Integer))
      ]
  ]
  where t p f goldFile = do r <- p defaultSMTCfg{verbose=True, redirectVerbose = Just goldFile} f
                            appendFile goldFile ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")

        empty :: (SymVal a, SymVal b) => b -> SArray a b
        empty = listArray []

        write :: (SymVal a, SymVal b) => SArray a b -> [(a, b)] -> SArray a b
        write = foldr (\(k, v) a -> writeArray a (literal k) (literal v))

{- HLint ignore module "Reduce duplication" -}
