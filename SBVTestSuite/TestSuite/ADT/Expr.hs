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

{-# LANGUAGE QuasiQuotes         #-}
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
    , goldenCapturedIO "adt_expr00" $ evalCheck (eval e00,  3)
    , goldenCapturedIO "adt_expr01" $ evalCheck (eval e01,  7)
    , goldenCapturedIO "adt_expr02" $ evalCheck (eval e02, 21)
    , goldenCapturedIO "adt_expr03" $ evalCheck (eval e03, 28)
    , goldenCapturedIO "adt_expr04" $ evalTest  (eval e04)
    , goldenCapturedIO "adt_expr05" $ evalTest  (eval e05)
    , goldenCapturedIO "adt_expr06" $ evalCheck (f (sVar (literal "a")), 0)
    , goldenCapturedIO "adt_expr07" $ evalCheck (f (sVar (literal "b")), 1)
    , goldenCapturedIO "adt_expr08" $ evalCheck (f (sVar (literal "c")), 1)
    , goldenCapturedIO "adt_expr09" $ evalCheck (f (sVar (literal "d")), 2)
    , goldenCapturedIO "adt_expr10" $ evalCheck (sum (map (f . sNum . literal) [-5 .. 9]),  45)
    , goldenCapturedIO "adt_expr11" $ evalCheck (sum (map (f . sNum . literal) [10]),        4)
    , goldenCapturedIO "adt_expr12" $ evalCheck (sum (map (f . sNum . literal) [11 .. 20]), 50)
    ]
    where a = literal "a"
          b = literal "a"

          e00 = 3                                -- 3
          e01 = 3 + 4                            -- 7
          e02 = e00 * e01                        -- 21
          e03 = sLet a e02 (sVar a + e01)        -- 28
          e04 = e03 + sLet a e03 (sVar a + e01)  -- 28 + 28 + 7 = 63
          e05 = sLet b e04 (sVar b * sVar b)     -- 63 * 63 = 3969

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

evalCheck :: SymVal a => (SBV a, a) -> FilePath -> IO ()
evalCheck (sv, v) rf = runSMTWith z3{verbose=True, redirectVerbose = Just rf} $ do
                        constrain $ sv ./= literal v
                        query $ do cs <- checkSat
                                   case cs of
                                     Unsat{} -> io $ appendFile rf $ "All good.\n"
                                     _       -> error $ "Unexpected: " ++ show cs

evalTest :: (Show a, SymVal a) => SBV a -> FilePath -> IO ()
evalTest sv rf = runSMTWith z3{verbose=True, redirectVerbose = Just rf} $ do
                    res <- free "res"
                    constrain $ sv .== res
                    query $ do cs <- checkSat
                               case cs of
                                 Sat -> do r <- getValue res
                                           io $ appendFile rf ("Result: " ++ show r ++ "\n")
                                 _       -> error $ "Unexpected: " ++ show cs

f :: SExpr -> SInteger
f e = [sCase|Expr e of
         Var s     | s .== literal "a"                       -> 0
                   | s .== literal "b" .|| s .== literal "c" -> 1
                   | sTrue                                   -> 2

         Num i     | i .<  10                                -> 3
                   | i .== 10                                -> 4
                   | i .>  10                                -> 5

         _                                                   -> 6
      |]
