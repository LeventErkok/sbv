-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Basics.PseudoBoolean
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test the pseudo-boolean functions
-----------------------------------------------------------------------------

module TestSuite.Basics.PseudoBoolean(tests)  where

import Data.SBV.Control
import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.pseudoBoolean" [
      goldenCapturedIO "pbAtMost"          $ \rf -> checkWith z3{redirectVerbose=Just rf} propPbAtMost
    , goldenCapturedIO "pbAtLeast"         $ \rf -> checkWith z3{redirectVerbose=Just rf} propPbAtLeast
    , goldenCapturedIO "pbExactly"         $ \rf -> checkWith z3{redirectVerbose=Just rf} propPbExactly
    , goldenCapturedIO "pbLe"              $ \rf -> checkWith z3{redirectVerbose=Just rf} propPbLe
    , goldenCapturedIO "pbGe"              $ \rf -> checkWith z3{redirectVerbose=Just rf} propPbGe
    , goldenCapturedIO "pbEq"              $ \rf -> checkWith z3{redirectVerbose=Just rf} propPbEq
    , goldenCapturedIO "pbMutexed"         $ \rf -> checkWith z3{redirectVerbose=Just rf} propPbMutexed
    , goldenCapturedIO "pbStronglyMutexed" $ \rf -> checkWith z3{redirectVerbose=Just rf} propPbStronglyMutexed
    ]

-- to test interactively, use:
--    checkWith z3 propPbAtLeast

checkWith :: SMTConfig -> ([SBool] -> SBool) -> IO ()
checkWith cfg spec = runSMTWith cfg{verbose=True} $ do
        bs <- sBools $ map (\i -> "b" ++ show i) [0..(9::Int)]
        constrain $ bnot (spec bs)
        query $ do cs <- checkSat
                   case cs of
                     Unsat -> return ()
                     Sat   -> getModel         >>= \r -> error $ "Failed! Expected Unsat, got SAT:\n" ++ show (SatResult (Satisfiable cfg r))
                     Unk   -> getUnknownReason >>= \r -> error $ "Failed! Expected Unsat, got UNK:\n" ++ show r

propPbAtMost :: [SBool] -> SBool
propPbAtMost bs = pbAtMost bs 8 .== (sum (map oneIf bs) .<= (8::SWord32))

propPbAtLeast :: [SBool] -> SBool
propPbAtLeast bs = pbAtLeast bs 5 .== (sum (map oneIf bs) .>= (5::SWord32))

propPbExactly :: [SBool] -> SBool
propPbExactly bs = pbExactly bs 5 .== (sum (map oneIf bs) .== (5::SWord32))

propPbLe :: [SBool] -> SBool
propPbLe bs = pbLe ibs 7 .== (sum (map valIf ibs) .<= (7::SInteger))
  where ibs = zip [1..] bs
        valIf (i, b) = ite b (literal (fromIntegral i)) 0

propPbGe :: [SBool] -> SBool
propPbGe bs = pbGe ibs 7 .== (sum (map valIf ibs) .>= (7::SInteger))
  where ibs = zip [1..] bs
        valIf (i, b) = ite b (literal (fromIntegral i)) 0

propPbEq :: [SBool] -> SBool
propPbEq bs = pbEq ibs 7 .== (sum (map valIf ibs) .== (7::SInteger))
  where ibs = zip [1..] bs
        valIf (i, b) = ite b (literal (fromIntegral i)) 0

propPbMutexed :: [SBool] -> SBool
propPbMutexed bs = pbMutexed bs .== (sum (map oneIf bs) .<= (1::SWord32))

propPbStronglyMutexed :: [SBool] -> SBool
propPbStronglyMutexed bs = pbStronglyMutexed bs .== (sum (map oneIf bs) .== (1::SWord32))
