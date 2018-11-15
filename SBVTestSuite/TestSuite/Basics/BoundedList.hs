-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Basics.BoundedList
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test the bounded sequence/list functions.
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.Basics.BoundedList(tests)  where

import Data.SBV.Control
import Utils.SBVTestFramework

import qualified Data.SBV.List as L
import qualified Data.SBV.List.Bounded as BL

import Control.Monad (unless)

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.List" [
      goldenCapturedIO "concreteFoldr"   $ \rf -> checkWith z3{redirectVerbose=Just rf} concreteFoldrSat   Sat
    , goldenCapturedIO "concreteFoldl"   $ \rf -> checkWith z3{redirectVerbose=Just rf} concreteFoldlSat   Sat
    , goldenCapturedIO "foldrAB1"        $ \rf -> checkWith z3{redirectVerbose=Just rf} (foldrAB 1)        Unsat
    , goldenCapturedIO "foldrAB2"        $ \rf -> checkWith z3{redirectVerbose=Just rf} (foldrAB 2)        Sat
    , goldenCapturedIO "foldrAB3"        $ \rf -> checkWith z3{redirectVerbose=Just rf} (foldrAB 3)        Sat
    , goldenCapturedIO "foldlABC1"       $ \rf -> checkWith z3{redirectVerbose=Just rf} (foldlABC 1)       Unsat
    , goldenCapturedIO "foldlABC2"       $ \rf -> checkWith z3{redirectVerbose=Just rf} (foldlABC 2)       Unsat
    , goldenCapturedIO "foldlABC3"       $ \rf -> checkWith z3{redirectVerbose=Just rf} (foldlABC 3)       Sat
    , goldenCapturedIO "concreteIbfoldr" $ \rf -> checkWith z3{redirectVerbose=Just rf} concreteIbfoldrSat Sat
    , goldenCapturedIO "ibfoldr"         $ \rf -> checkWith z3{redirectVerbose=Just rf} ibfoldrSat         Sat
    , goldenCapturedIO "concreteIbfoldl" $ \rf -> checkWith z3{redirectVerbose=Just rf} concreteIbfoldlSat Sat
    , goldenCapturedIO "ibfoldl"         $ \rf -> checkWith z3{redirectVerbose=Just rf} ibfoldlUnsat       Unsat
    , goldenCapturedIO "concreteReverse" $ \rf -> checkWith z3{redirectVerbose=Just rf} concreteReverseSat Sat
    , goldenCapturedIO "reverse"         $ \rf -> checkWith z3{redirectVerbose=Just rf} reverseSat         Sat
    , goldenCapturedIO "concreteSort"    $ \rf -> checkWith z3{redirectVerbose=Just rf} concreteSortSat    Sat
    , goldenCapturedIO "sort"            $ \rf -> checkWith z3{redirectVerbose=Just rf} sortSat            Sat
    ]

checkWith :: SMTConfig -> Symbolic () -> CheckSatResult -> IO ()
checkWith cfg props csExpected = runSMTWith cfg{verbose=True} $ do
        _ <- props
        query $ do cs <- checkSat
                   unless (cs == csExpected) $
                     case cs of
                       Unsat -> error "Failed! Expected Sat, got UNSAT"
                       Sat   -> getModel         >>= \r -> error $ "Failed! Expected Unsat, got SAT:\n" ++ show (SatResult (Satisfiable cfg r))
                       Unk   -> getUnknownReason >>= \r -> error $ "Failed! Expected Unsat, got UNK:\n" ++ show r

concreteFoldrSat :: Symbolic ()
concreteFoldrSat = constrain $ BL.bfoldr 3 (+) 0 [1..3] .== (6 :: SInteger)

concreteFoldlSat :: Symbolic ()
concreteFoldlSat = constrain $ BL.bfoldl 10 (+) 0 [1..3] .== (6 :: SInteger)

-- unsatisfiable at bound = 1, satisfiable at bound = 2 or bound = 3
foldrAB :: Int -> Symbolic ()
foldrAB bound = do
  [a, b] <- sIntegers ["a", "b"]
  constrain $ a .> 0
  constrain $ b .> 0
  constrain $ BL.bfoldr bound (+) 0 (L.implode [a, b]) .== a + b

-- unsatisfiable at bound = 1 or bound = 2, satisfiable at bound = 3
foldlABC :: Int -> Symbolic ()
foldlABC bound = do
  [a, b, c] <- sIntegers ["a", "b", "c"]
  constrain $ a .> 0
  constrain $ b .> 0
  constrain $ c .> 0
  constrain $ BL.bfoldr bound (+) 0 (L.implode [a, b, c]) .== a + b + c

concreteIbfoldrSat :: Symbolic ()
concreteIbfoldrSat = constrain $
  BL.ibfoldr 10 (\i a b -> if i == 6 then a else b) (-1) [0..9]
  .==
  (6 :: SInteger)

ibfoldrSat :: Symbolic ()
ibfoldrSat = do
  abcd <- sIntegers ["a", "b", "c", "d"]
  constrain $ BL.ibfoldr 10
    (\i a' b' -> (fromIntegral i .== a') &&& b')
    true
    (L.implode abcd)

concreteIbfoldlSat :: Symbolic ()
concreteIbfoldlSat = constrain $
  BL.ibfoldl 10 (\i b a -> if i == 6 then a else b) (-1) [0..9]
  .==
  (6 :: SInteger)

-- unsatisfiable
ibfoldlUnsat :: Symbolic ()
ibfoldlUnsat = do
  abcd@[_, _, c, _] <- sIntegers ["a", "b", "c", "d"]
  constrain $ BL.ibfoldl 10
    (\i a' b' -> a' &&& ite (fromIntegral i .== (2 :: SBV Integer)) (b' .== 42) true)
    true
    (L.implode abcd)
  constrain $ c .== 43

concreteReverseSat :: Symbolic ()
concreteReverseSat = constrain $
  BL.breverse 10 [1..10] .== ([10,9..1] :: SList Integer)

reverseSat :: Symbolic ()
reverseSat = do
  abcd <- sIntegers ["a", "b", "c", "d"]
  constrain $ BL.breverse 10 (L.implode abcd) .== L.implode (reverse abcd)

concreteSortSat :: Symbolic ()
concreteSortSat = constrain $
  BL.bsort 10 [5,6,3,8,9,2,1,7,10,4]
  .==
  ([1..10] :: SList Integer)

sortSat :: Symbolic ()
sortSat = do
  [a, b, c] <- sIntegers ["a", "b", "c"]
  let sorted = BL.bsort 3 $ L.implode [a, b, c]
      inconsistent = false

  constrain $
    ite (a .< b)
      (ite (a .< c)
        (ite (b .< c)
          (sorted .== L.implode [a, b, c])
          (sorted .== L.implode [a, c, b]))
        (ite (b .< c)
          (sorted .== L.implode [c, a, b])
          inconsistent))
      (ite (a .< c)
        (ite (b .< c)
          (sorted .== L.implode [b, a, c])
          inconsistent)
        (ite (b .< c)
          (sorted .== L.implode [b, c, a])
          (sorted .== L.implode [c, b, a])))
