-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.BoundedList
-- Copyright : (c) Joel Burget
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test the bounded sequence/list functions.
-----------------------------------------------------------------------------

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE ScopedTypeVariables        #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.BoundedList(tests)  where

import Data.SBV.Control
import Utils.SBVTestFramework

import Prelude hiding ((!!))
import Data.SBV.List ((.:), (!!))
import qualified Data.SBV.List as L
import qualified Data.SBV.Tools.BoundedList as BL

import Control.Monad (unless)
import Control.Monad.State (MonadState(..), State, modify, runState)

-- | Flag to mark a failed computation
newtype Failure = Failure SBool
  deriving (Mergeable, EqSymbolic)

-- | Evaluation monad with failure
newtype Eval a = Eval { unEval :: State Failure a }
  deriving (Functor, Applicative, Monad, MonadState Failure)

runEval :: Eval a -> (a, Failure)
runEval (Eval eval) = runState eval (Failure sFalse)

instance Mergeable a => Mergeable (Eval a) where
  symbolicMerge force test left right = Eval $ state $ \s0 ->
    let (resL, sL) = runState (unEval left)  s0
        (resR, sR) = runState (unEval right) s0
    in ( symbolicMerge force test resL resR
       , symbolicMerge force test sL   sR
       )

markFailure :: SBool -> Eval ()
markFailure failure = modify (\(Failure b) -> Failure (b .|| failure))

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.BoundedList" [
      goldenCapturedIO "concreteFoldr"   $ \rf -> checkWith z3{redirectVerbose=Just rf} concreteFoldrSat   Sat
    , goldenCapturedIO "concreteFoldl"   $ \rf -> checkWith z3{redirectVerbose=Just rf} concreteFoldlSat   Sat
    , goldenCapturedIO "foldrAB1"        $ \rf -> checkWith z3{redirectVerbose=Just rf} (foldrAB 1)        Unsat
    , goldenCapturedIO "foldrAB2"        $ \rf -> checkWith z3{redirectVerbose=Just rf} (foldrAB 2)        Sat
    , goldenCapturedIO "foldrAB3"        $ \rf -> checkWith z3{redirectVerbose=Just rf} (foldrAB 3)        Sat
    , goldenCapturedIO "foldlABC1"       $ \rf -> checkWith z3{redirectVerbose=Just rf} (foldlABC 1)       Unsat
    , goldenCapturedIO "foldlABC2"       $ \rf -> checkWith z3{redirectVerbose=Just rf} (foldlABC 2)       Unsat
    , goldenCapturedIO "foldlABC3"       $ \rf -> checkWith z3{redirectVerbose=Just rf} (foldlABC 3)       Sat
    , goldenCapturedIO "concreteReverse" $ \rf -> checkWith z3{redirectVerbose=Just rf} concreteReverseSat Sat
    , goldenCapturedIO "reverse"         $ \rf -> checkWith z3{redirectVerbose=Just rf} reverseSat         Sat
    , goldenCapturedIO "reverseAlt10"    $ \rf -> checkWith z3{redirectVerbose=Just rf} (reverseAlt 10)    Unsat
    , goldenCapturedIO "concreteSort"    $ \rf -> checkWith z3{redirectVerbose=Just rf} concreteSortSat    Sat
    , goldenCapturedIO "sort"            $ \rf -> checkWith z3{redirectVerbose=Just rf} sortSat            Sat
    , goldenCapturedIO "mapWithFailure"  $ \rf -> checkWith z3{redirectVerbose=Just rf} mapWithFailure     Sat
    , goldenCapturedIO "mapNoFailure"    $ \rf -> checkWith z3{redirectVerbose=Just rf} mapNoFailure       Unsat
    , goldenCapturedIO "maxlWithFailure" $ \rf -> checkWith z3{redirectVerbose=Just rf} maxlWithFailure    Sat
    , goldenCapturedIO "maxrWithFailure" $ \rf -> checkWith z3{redirectVerbose=Just rf} maxrWithFailure    Sat
    ]

checkWith :: SMTConfig -> Symbolic () -> CheckSatResult -> IO ()
checkWith cfg props csExpected = runSMTWith cfg{verbose=True} $ do
        _ <- props
        query $ do cs <- checkSat
                   unless (cs == csExpected) $
                     case cs of
                       Unsat  -> error $ "Failed! Expected " ++ show csExpected ++ ", got Unsat"
                       DSat{} -> error $ "Failed! Expected " ++ show csExpected ++ ", got delta-sat"
                       Sat    -> getModel         >>= \r -> error $ "Failed! Expected " ++ show csExpected ++ ", got Sat:\n" ++ show (SatResult (Satisfiable cfg r))
                       Unk    -> getUnknownReason >>= \r -> error $ "Failed! Expected " ++ show csExpected ++ ", got Unk:\n" ++ show r

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

concreteReverseSat :: Symbolic ()
concreteReverseSat = constrain $ BL.breverse 10 [1..10] .== ([10,9..1] :: SList Integer)

reverseSat :: Symbolic ()
reverseSat = do
  abcd <- sIntegers ["a", "b", "c", "d"]
  constrain $ BL.breverse 10 (L.implode abcd) .== L.implode (reverse abcd)

reverseAlt :: Int -> Symbolic ()
reverseAlt i = do
  xs <- sList "xs"

  -- Assert the negation; so Unsat response means it's all good!
  constrain $ BL.breverse i xs ./= rev i xs ([] :: SList Integer)
 where  -- classic reverse with accumulator
       rev 0 _  sofar = sofar
       rev c xs sofar = ite (L.null xs)
                            sofar
                            (rev (c-1) (L.tail xs) (L.head xs .: sofar))


concreteSortSat :: Symbolic ()
concreteSortSat = constrain $ BL.bsort 10 [5,6,3,8,9,2,1,7,10,4] .== ([1..10] :: SList Integer)

sortSat :: Symbolic ()
sortSat = do [a, b, c] <- sIntegers ["a", "b", "c"]

             let sorted = BL.bsort 3 $ L.implode [a, b, c]

                 ordered :: (SInteger, SInteger, SInteger) -> SBool
                 ordered (x, y, z) = x .<= y .&& y .<= z

             constrain $ ordered (a, b, c) .=> sorted .== L.implode [a, b, c]
             constrain $ ordered (a, c, b) .=> sorted .== L.implode [a, c, b]
             constrain $ ordered (b, a, c) .=> sorted .== L.implode [b, a, c]
             constrain $ ordered (b, c, a) .=> sorted .== L.implode [b, c, a]
             constrain $ ordered (c, a, b) .=> sorted .== L.implode [c, a, b]
             constrain $ ordered (c, b, a) .=> sorted .== L.implode [c, b, a]

-- | Increment, failing if a value lies outside of [0, 10]
boundedIncr :: SList Integer -> Eval (SList Integer)
boundedIncr = BL.bmapM 10 $ \i -> do
  markFailure $ i .< 0 .|| i .> 10
  pure $ i + 1

-- | Max (based on foldr), failing if a value lies outside of [0, 10]
boundedMaxr :: SList Integer -> Eval SInteger
boundedMaxr = BL.bfoldrM 10
  (\i maxi -> do
    markFailure $ i .< 0 .|| i .> 10
    pure $ smax i maxi)
  0

-- | Max (based on foldl), failing if a value lies outside of [0, 10]
boundedMaxl :: SList Integer -> Eval SInteger
boundedMaxl = BL.bfoldlM 10
  (\maxi i -> do
    markFailure $ i .< 0 .|| i .> 10
    pure $ smax i maxi)
  0

-- the mapping will have failed if one of the resulting values is greater than
-- 11
mapWithFailure :: Symbolic ()
mapWithFailure = do
  lst <- sList "ints"
  let (lst', failure) = runEval $ boundedIncr lst
  constrain $ lst' !! 2 .> 11 .=> failure .== Failure sTrue

-- mapping over these values of a, b, and c cannot fail (this is unsat)
mapNoFailure :: Symbolic ()
mapNoFailure = do
  [a, b, c] <- sIntegers ["a", "b", "c"]
  let (_lst', Failure failure) = runEval $ boundedIncr $ L.implode [a, b, c]
  constrain $ a + b + c .== 6
  constrain $ a .> 0 .&& b .> 0 .&& c .> 0
  constrain failure

-- boundedMaxl fails if one of the values is too big
maxlWithFailure :: Symbolic ()
maxlWithFailure = do
  lst <- sList "ints"
  let (maxi, Failure failure) = runEval $ boundedMaxl lst
  constrain $ maxi .> 10 .=> failure

-- boundedMaxl fails if one of the values is too big
maxrWithFailure :: Symbolic ()
maxrWithFailure = do
  lst <- sList "ints"
  let (maxi, Failure failure) = runEval $ boundedMaxr lst
  constrain $ maxi .> 10 .=> failure
