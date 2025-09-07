-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.ADT.Expr
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing ADTs, expressions
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.ADT.Expr(tests) where

import Data.SBV
import Data.SBV.Control
import Utils.SBVTestFramework

import Documentation.SBV.Examples.ADT.Basic

tests :: TestTree
tests =
  testGroup "ADT" [
      goldenCapturedIO "adt_gen00"  t00
    , goldenCapturedIO "adt_expr00" $ evalTest (eval e00,  3)
    , goldenCapturedIO "adt_expr01" $ evalTest (eval e01,  7)
    , goldenCapturedIO "adt_expr02" $ evalTest (eval e02, 21)
    ]
    where e00 = 3
          e01 = 3 + 4
          e02 = e00 * e01

-- Create something like:
--       let a = _
--    in let b = _
--    in _ + _
-- such that it evaluates to 12
t00 :: FilePath -> IO ()
t00 rf = runSMTWith z3{verbose=True, redirectVerbose = Just rf} $ do
            a :: SExpr <- free "a"
            constrain $ isValid a
            constrain $ eval a .== 12

            constrain $ isLet a
            constrain $ isLet (getLet_3 a)
            constrain $ isAdd (getLet_3 (getLet_3 a))

            query $ do cs <- checkSat
                       case cs of
                         Sat{} -> do v <- getValue a
                                     io $ do appendFile rf $ "\nGot: " ++ show v
                                             appendFile rf   "\nDONE\n"
                         _     -> error $ "Unexpected: " ++ show cs

evalTest :: SymVal a => (SBV a, a) -> FilePath -> IO ()
evalTest (sv, v) rf = runSMTWith z3{verbose=True, redirectVerbose = Just rf} $ do
                        constrain $ sv ./= literal v
                        query $ do cs <- checkSat
                                   case cs of
                                     Unsat{} -> io $ do appendFile rf $ "All good."
                                     _       -> error $ "Unexpected: " ++ show cs
