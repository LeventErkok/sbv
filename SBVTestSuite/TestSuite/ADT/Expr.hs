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

{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.ADT.Expr(tests) where

import Control.Monad (void)

import Data.SBV
import Data.SBV.Control
import Utils.SBVTestFramework

import Documentation.SBV.Examples.ADT.Expr

-- Testing constructor/type name conflct
data A = A Integer
       | B Word8
       | C A A
       deriving Show

mkSymbolic [''A]

tests :: TestTree
tests =
  testGroup "ADT" [
      goldenCapturedIO "adt_expr00c" $ evalCheck  (eval e00,  3)
    , goldenCapturedIO "adt_expr00"  $ evalCheckS eval (e00,  3)

    , goldenCapturedIO "adt_expr01c" $ evalCheck  (eval e01,  7)
    , goldenCapturedIO "adt_expr01"  $ evalCheckS eval (e01,  7)

    , goldenCapturedIO "adt_expr02c" $ evalCheck  (eval e02, 21)
    , goldenCapturedIO "adt_expr02"  $ evalCheckS eval (e02, 21)

    , goldenCapturedIO "adt_expr03c" $ evalCheck  (eval e03, 28)
    , goldenCapturedIO "adt_expr03"  $ evalCheckS eval (e03, 28)

    , goldenCapturedIO "adt_expr04" $ evalTest  (eval e04)
    , goldenCapturedIO "adt_expr05" $ evalTest  (eval e05)

    , goldenCapturedIO "adt_expr06c" $ evalCheck  (f (sVar (literal "a")), 0)
    , goldenCapturedIO "adt_expr06"  $ evalCheckS f  (sVar (literal "a") , 0)

    , goldenCapturedIO "adt_expr07c" $ evalCheck  (f (sVar (literal "b")), 1)
    , goldenCapturedIO "adt_expr07"  $ evalCheckS f  (sVar (literal "b") , 1)

    , goldenCapturedIO "adt_expr08c" $ evalCheck  (f (sVar (literal "c")), 1)
    , goldenCapturedIO "adt_expr08"  $ evalCheckS f  (sVar (literal "c") , 1)

    , goldenCapturedIO "adt_expr09c" $ evalCheck  (f (sVar (literal "d")), 2)
    , goldenCapturedIO "adt_expr09"  $ evalCheckS f  (sVar (literal "d") , 2)

    , goldenCapturedIO "adt_expr10c" $ evalCheck   (sum (map (f . sVal . literal)      [-5 .. 9]),  45)
    , goldenCapturedIO "adt_expr10"  $ evalCheckSL (sum . map f) (map (sVal . literal) [-5 .. 9],   45)

    , goldenCapturedIO "adt_expr11c" $ evalCheck   (sum (map (f . sVal . literal)      [10, 10]),    8)
    , goldenCapturedIO "adt_expr11"  $ evalCheckSL (sum . map f) (map (sVal . literal) [10, 10],     8)

    , goldenCapturedIO "adt_expr12c" $ evalCheck   (sum (map (f . sVal . literal)      [11 .. 20]), 50)
    , goldenCapturedIO "adt_expr12"  $ evalCheckSL (sum . map f) (map (sVal . literal) [11 .. 20],  50)

    , goldenCapturedIO "adt_expr13c" $ evalCheck  (f e00, 3)
    , goldenCapturedIO "adt_expr13"  $ evalCheckS f (e00, 3)

    , goldenCapturedIO "adt_expr14c" $ evalCheck  (f e01, 6)
    , goldenCapturedIO "adt_expr14"  $ evalCheckS f (e01, 6)

    , goldenCapturedIO "adt_expr15c" $ evalCheck  (f e02, 6)
    , goldenCapturedIO "adt_expr15"  $ evalCheckS f (e02, 6)

    , goldenCapturedIO "adt_expr16c" $ evalCheck  (f e03, 6)
    , goldenCapturedIO "adt_expr16"  $ evalCheckS f (e03, 6)

    , goldenCapturedIO "adt_expr17c" $ evalCheck  (f e04, 6)
    , goldenCapturedIO "adt_expr17"  $ evalCheckS f (e04, 6)

    , goldenCapturedIO "adt_expr18c" $ evalCheck  (f e05, 6)
    , goldenCapturedIO "adt_expr18"  $ evalCheckS f (e05, 6)

    , goldenCapturedIO "adt_gen00"  t00
    , goldenCapturedIO "adt_gen01"  $ tSat (-1)
    , goldenCapturedIO "adt_gen02"  $ tSat 0
    , goldenCapturedIO "adt_gen03"  $ tSat 1
    , goldenCapturedIO "adt_gen04"  $ tSat 2
    , goldenCapturedIO "adt_gen05"  $ tSat 3
    , goldenCapturedIO "adt_gen06"  $ tSat 4
    , goldenCapturedIO "adt_gen07"  $ tSat 5
    , goldenCapturedIO "adt_gen08"  $ tSat 6
    , goldenCapturedIO "adt_gen09"  $ tSat 7
    , goldenCapturedIO "adt_gen10"  $ tSat 8
    , goldenCapturedIO "adt_gen11"  $ tSat 9
    , goldenCapturedIO "adt_gen12"  $ tSat 100
    , goldenCapturedIO "adt_chk01"  $ evalTest (t (sA 12))

    -- Nested pattern tests: h is a simplifier using nested patterns
    -- Add (Val 0) e => e
    , goldenCapturedIO "adt_nested00c" $ evalCheck (h (sAdd (sVal 0) (sVal 5)),  sVal 5)
    , goldenCapturedIO "adt_nested00"  $ evalCheckS h (sAdd (sVal 0) (sVal 5),   sVal 5)
    -- Add e (Val 0) => e
    , goldenCapturedIO "adt_nested01c" $ evalCheck (h (sAdd (sVal 7) (sVal 0)),  sVal 7)
    , goldenCapturedIO "adt_nested01"  $ evalCheckS h (sAdd (sVal 7) (sVal 0),   sVal 7)
    -- Mul (Val 1) e => e
    , goldenCapturedIO "adt_nested02c" $ evalCheck (h (sMul (sVal 1) (sVal 9)),  sVal 9)
    , goldenCapturedIO "adt_nested02"  $ evalCheckS h (sMul (sVal 1) (sVal 9),   sVal 9)
    -- Mul e (Val 1) => e
    , goldenCapturedIO "adt_nested03c" $ evalCheck (h (sMul (sVal 4) (sVal 1)),  sVal 4)
    , goldenCapturedIO "adt_nested03"  $ evalCheckS h (sMul (sVal 4) (sVal 1),   sVal 4)
    -- Mul (Val 0) _ => 0
    , goldenCapturedIO "adt_nested04c" $ evalCheck (h (sMul (sVal 0) (sVal 99)), sVal 0)
    , goldenCapturedIO "adt_nested04"  $ evalCheckS h (sMul (sVal 0) (sVal 99),  sVal 0)
    -- No simplification applies: Add (Val 3) (Val 4) stays as-is
    , goldenCapturedIO "adt_nested05c" $ evalCheck (h (sAdd (sVal 3) (sVal 4)),  sAdd (sVal 3) (sVal 4))
    , goldenCapturedIO "adt_nested05"  $ evalCheckS h (sAdd (sVal 3) (sVal 4),   sAdd (sVal 3) (sVal 4))
    -- Guard miss: Add (Val 1) e, i /= 0, falls through to _
    , goldenCapturedIO "adt_nested06c" $ evalCheck (h (sAdd (sVal 1) (sVal 5)),  sAdd (sVal 1) (sVal 5))
    , goldenCapturedIO "adt_nested06"  $ evalCheckS h (sAdd (sVal 1) (sVal 5),   sAdd (sVal 1) (sVal 5))
    -- Pattern ordering: Add (Val 0) (Val 0) => Val 0 (first rule fires, not second)
    , goldenCapturedIO "adt_nested07c" $ evalCheck (h (sAdd (sVal 0) (sVal 0)),  sVal 0)
    , goldenCapturedIO "adt_nested07"  $ evalCheckS h (sAdd (sVal 0) (sVal 0),   sVal 0)
    -- Mul (Val 1) e where e is compound: result is the compound expression
    , goldenCapturedIO "adt_nested08c" $ evalCheck (h (sMul (sVal 1) (sAdd (sVal 3) (sVal 4))),  sAdd (sVal 3) (sVal 4))
    , goldenCapturedIO "adt_nested08"  $ evalCheckS h (sMul (sVal 1) (sAdd (sVal 3) (sVal 4)),   sAdd (sVal 3) (sVal 4))
    -- Mul (Val 0) e where e is compound: result is Val 0 regardless of right side
    , goldenCapturedIO "adt_nested09c" $ evalCheck (h (sMul (sVal 0) (sAdd (sVal 3) (sVal 4))),  sVal 0)
    , goldenCapturedIO "adt_nested09"  $ evalCheckS h (sMul (sVal 0) (sAdd (sVal 3) (sVal 4)),   sVal 0)
    -- Non-Add/Mul constructor: Var falls through to _
    , goldenCapturedIO "adt_nested10c" $ evalCheck (h (sVar (literal "x")),  sVar (literal "x"))
    , goldenCapturedIO "adt_nested10"  $ evalCheckS h (sVar (literal "x"),   sVar (literal "x"))
    -- Non-Add/Mul constructor: Val falls through to _
    , goldenCapturedIO "adt_nested11c" $ evalCheck (h (sVal 42),  sVal 42)
    , goldenCapturedIO "adt_nested11"  $ evalCheckS h (sVal 42,   sVal 42)
    -- Let falls through to _
    , goldenCapturedIO "adt_nested12c" $ evalCheck (h (sLet (literal "x") (sVal 1) (sVar (literal "x"))),  sLet (literal "x") (sVal 1) (sVar (literal "x")))
    , goldenCapturedIO "adt_nested12"  $ evalCheckS h (sLet (literal "x") (sVal 1) (sVar (literal "x")),   sLet (literal "x") (sVal 1) (sVar (literal "x")))
    -- Mul (Val 0) with a non-Val right side (Var): result is Val 0, wildcard ignores it
    , goldenCapturedIO "adt_nested13c" $ evalCheck (h (sMul (sVal 0) (sVar (literal "x"))),  sVal 0)
    , goldenCapturedIO "adt_nested13"  $ evalCheckS h (sMul (sVal 0) (sVar (literal "x")),   sVal 0)
    -- Add (Val 0) with a compound right side (Add)
    , goldenCapturedIO "adt_nested14c" $ evalCheck (h (sAdd (sVal 0) (sMul (sVal 2) (sVal 3))),  sMul (sVal 2) (sVal 3))
    , goldenCapturedIO "adt_nested14"  $ evalCheckS h (sAdd (sVal 0) (sMul (sVal 2) (sVal 3)),   sMul (sVal 2) (sVal 3))
    -- Idempotency: h (h e) == h e (using a simplifiable input)
    , goldenCapturedIO "adt_nested15c" $ evalCheck (h (h (sAdd (sVal 0) (sVal 5))),  sVal 5)
    , goldenCapturedIO "adt_nested15"  $ evalCheckS (h . h) (sAdd (sVal 0) (sVal 5),  sVal 5)
    -- Idempotency: h (h e) == h e (using a non-simplifiable input)
    , goldenCapturedIO "adt_nested16c" $ evalCheck (h (h (sAdd (sVal 3) (sVal 4))),  sAdd (sVal 3) (sVal 4))
    , goldenCapturedIO "adt_nested16"  $ evalCheckS (h . h) (sAdd (sVal 3) (sVal 4),  sAdd (sVal 3) (sVal 4))
    -- Two-step simplification: h (h (Mul (Val 1) (Add (Val 0) (Val 5)))) => Val 5
    -- First h: Mul (Val 1) (Add (Val 0) (Val 5)) => Add (Val 0) (Val 5)
    -- Second h: Add (Val 0) (Val 5)              => Val 5
    , goldenCapturedIO "adt_nested17c" $ evalCheck (h (h (sMul (sVal 1) (sAdd (sVal 0) (sVal 5)))),  sVal 5)
    , goldenCapturedIO "adt_nested17"  $ evalCheckS (h . h) (sMul (sVal 1) (sAdd (sVal 0) (sVal 5)),  sVal 5)
    -- Semantics preservation: eval (h e) == eval e for all closed e
    , goldenCapturedIO "adt_nested18"  hPreservesEval
    -- Mul rule ordering: Mul (Val 1) (Val 1) => Val 1 (first Mul rule fires, not second)
    , goldenCapturedIO "adt_nested19c" $ evalCheck (h (sMul (sVal 1) (sVal 1)),  sVal 1)
    , goldenCapturedIO "adt_nested19"  $ evalCheckS h (sMul (sVal 1) (sVal 1),   sVal 1)
    -- Guard miss on both Mul rules: Mul (Val 2) (Val 3) falls through to _
    , goldenCapturedIO "adt_nested20c" $ evalCheck (h (sMul (sVal 2) (sVal 3)),  sMul (sVal 2) (sVal 3))
    , goldenCapturedIO "adt_nested20"  $ evalCheckS h (sMul (sVal 2) (sVal 3),   sMul (sVal 2) (sVal 3))
    -- Mul (Val 1) (Var "x") => Var "x": Mul rule returns a non-Val expression
    , goldenCapturedIO "adt_nested21c" $ evalCheck (h (sMul (sVal 1) (sVar (literal "x"))),  sVar (literal "x"))
    , goldenCapturedIO "adt_nested21"  $ evalCheckS h (sMul (sVal 1) (sVar (literal "x")),   sVar (literal "x"))
    -- Add (Val 0) (Var "x") => Var "x": Add rule returns a non-Val expression
    , goldenCapturedIO "adt_nested22c" $ evalCheck (h (sAdd (sVal 0) (sVar (literal "x"))),  sVar (literal "x"))
    , goldenCapturedIO "adt_nested22"  $ evalCheckS h (sAdd (sVal 0) (sVar (literal "x")),   sVar (literal "x"))
    -- Focused proof: h preserves eval for Add expressions specifically
    , goldenCapturedIO "adt_nested23"  hPreservesEvalAdd
    -- Focused proof: h preserves eval for Mul expressions specifically
    , goldenCapturedIO "adt_nested24"  hPreservesEvalMul

    -- Deep nesting: cfold constant-folds Add (Mul (Val a) (Val b)) (Mul (Val c) (Val d)) => Val (a*b + c*d)
    -- 4-level deep nested pattern on all branches simultaneously
    -- Fires: Add (Mul (Val 2) (Val 3)) (Mul (Val 4) (Val 5)) => Val 26
    , goldenCapturedIO "adt_nested25c" $ evalCheck (cfold (sAdd (sMul (sVal 2) (sVal 3)) (sMul (sVal 4) (sVal 5))),  sVal 26)
    , goldenCapturedIO "adt_nested25"  $ evalCheckS cfold (sAdd (sMul (sVal 2) (sVal 3)) (sMul (sVal 4) (sVal 5)),   sVal 26)
    -- Fires: Add (Mul (Val 0) (Val 99)) (Mul (Val 1) (Val 1)) => Val 1
    , goldenCapturedIO "adt_nested26c" $ evalCheck (cfold (sAdd (sMul (sVal 0) (sVal 99)) (sMul (sVal 1) (sVal 1))),  sVal 1)
    , goldenCapturedIO "adt_nested26"  $ evalCheckS cfold (sAdd (sMul (sVal 0) (sVal 99)) (sMul (sVal 1) (sVal 1)),   sVal 1)
    -- No match: right branch is Var, not Mul (Val _) (Val _)
    , goldenCapturedIO "adt_nested27c" $ evalCheck (cfold (sAdd (sMul (sVal 2) (sVal 3)) (sVar (literal "x"))),  sAdd (sMul (sVal 2) (sVal 3)) (sVar (literal "x")))
    , goldenCapturedIO "adt_nested27"  $ evalCheckS cfold (sAdd (sMul (sVal 2) (sVal 3)) (sVar (literal "x")),   sAdd (sMul (sVal 2) (sVal 3)) (sVar (literal "x")))
    -- No match: outer constructor is Mul, not Add
    , goldenCapturedIO "adt_nested28c" $ evalCheck (cfold (sMul (sVal 2) (sVal 3)),  sMul (sVal 2) (sVal 3))
    , goldenCapturedIO "adt_nested28"  $ evalCheckS cfold (sMul (sVal 2) (sVal 3),   sMul (sVal 2) (sVal 3))
    -- Semantics preservation: eval (cfold e) == eval e for all e
    , goldenCapturedIO "adt_nested29"  cfoldPreservesEval

    -- Pipeline tests: cfold (h e) — first simplify with h, then constant-fold with cfold
    -- Neither h nor cfold fires: Add (Mul (Val 2) (Val 3)) (Mul (Val 4) (Val 5)) passes through h unchanged, cfold folds to Val 26
    , goldenCapturedIO "adt_nested30c" $ evalCheck (cfold (h (sAdd (sMul (sVal 2) (sVal 3)) (sMul (sVal 4) (sVal 5)))),  sVal 26)
    , goldenCapturedIO "adt_nested30"  $ evalCheckS (cfold . h) (sAdd (sMul (sVal 2) (sVal 3)) (sMul (sVal 4) (sVal 5)),  sVal 26)
    -- h leaves outer Add unchanged; cfold still sees Add (Mul (Val 1) (Val 2)) (Mul (Val 0) (Val 4)) and folds to Val 2
    , goldenCapturedIO "adt_nested31c" $ evalCheck (cfold (h (sAdd (sMul (sVal 1) (sVal 2)) (sMul (sVal 0) (sVal 4)))),  sVal 2)
    , goldenCapturedIO "adt_nested31"  $ evalCheckS (cfold . h) (sAdd (sMul (sVal 1) (sVal 2)) (sMul (sVal 0) (sVal 4)),  sVal 2)
    -- h fires (Mul (Val 1) r => r), exposing a cfold-able expression; cfold then folds to Val 26
    , goldenCapturedIO "adt_nested32c" $ evalCheck (cfold (h (sMul (sVal 1) (sAdd (sMul (sVal 2) (sVal 3)) (sMul (sVal 4) (sVal 5))))),  sVal 26)
    , goldenCapturedIO "adt_nested32"  $ evalCheckS (cfold . h) (sMul (sVal 1) (sAdd (sMul (sVal 2) (sVal 3)) (sMul (sVal 4) (sVal 5))),  sVal 26)
    -- h fires (Add (Val 0) r => r), exposing a cfold-able expression; cfold then folds to Val 26
    , goldenCapturedIO "adt_nested33c" $ evalCheck (cfold (h (sAdd (sVal 0) (sAdd (sMul (sVal 2) (sVal 3)) (sMul (sVal 4) (sVal 5))))),  sVal 26)
    , goldenCapturedIO "adt_nested33"  $ evalCheckS (cfold . h) (sAdd (sVal 0) (sAdd (sMul (sVal 2) (sVal 3)) (sMul (sVal 4) (sVal 5))),  sVal 26)
    -- Semantics preservation of the pipeline: eval (cfold (h e)) == eval e for all e
    , goldenCapturedIO "adt_nested34"  cfoldAfterHPreservesEval

    -- Literal pattern tests: p uses integer and string literal patterns
    -- Top-level literal fires: Val 0 => 100
    , goldenCapturedIO "adt_lit00c" $ evalCheck (p (sVal 0),  100)
    , goldenCapturedIO "adt_lit00"  $ evalCheckS p (sVal 0,   100)
    -- Top-level literal fires: Val 1 => 200
    , goldenCapturedIO "adt_lit01c" $ evalCheck (p (sVal 1),  200)
    , goldenCapturedIO "adt_lit01"  $ evalCheckS p (sVal 1,   200)
    -- Top-level literal misses: Val 2 falls through to eval e = 2
    , goldenCapturedIO "adt_lit02c" $ evalCheck (p (sVal 2),  2)
    , goldenCapturedIO "adt_lit02"  $ evalCheckS p (sVal 2,   2)
    -- Nested literal fires: Add (Val 0) (Val 5) => eval (Val 5) = 5
    , goldenCapturedIO "adt_lit03c" $ evalCheck (p (sAdd (sVal 0) (sVal 5)),  5)
    , goldenCapturedIO "adt_lit03"  $ evalCheckS p (sAdd (sVal 0) (sVal 5),   5)
    -- Nested literal misses: Add (Val 1) (Val 5) => eval e = 6
    , goldenCapturedIO "adt_lit04c" $ evalCheck (p (sAdd (sVal 1) (sVal 5)),  6)
    , goldenCapturedIO "adt_lit04"  $ evalCheckS p (sAdd (sVal 1) (sVal 5),   6)
    -- Var falls through to eval e (= 0 for unbound var)
    , goldenCapturedIO "adt_lit05c" $ evalCheck (p (sVar (literal "x")),  0)
    , goldenCapturedIO "adt_lit05"  $ evalCheckS p (sVar (literal "x"),   0)
    ]
    where a = literal "a"
          b = literal "a"

          e00 = 3                                -- 3
          e01 = 3 + 4                            -- 7
          e02 = e00 * e01                        -- 21
          e03 = sLet a e02 (sVar a + e01)        -- 28
          e04 = e03 + sLet a e03 (sVar a + e01)  -- 28 + 28 + 7 = 63
          e05 = sLet b e04 (sVar b * sVar b)     -- 63 * 63 = 3969

evalCheck :: SymVal a => (SBV a, SBV a) -> FilePath -> IO ()
evalCheck (sv, v) rf = runSMTWith z3{verbose=True, redirectVerbose = Just rf} $ do
                        constrain $ sv ./= v
                        query $ do cs <- checkSat
                                   case cs of
                                     Unsat{} -> io $ appendFile rf "All good.\n"
                                     _       -> error $ "Unexpected: " ++ show cs

evalCheckS :: SymVal b => (SExpr -> SBV b) -> (SExpr, SBV b) -> FilePath -> IO ()
evalCheckS fun (e, v) rf = runSMTWith z3{verbose=True, redirectVerbose = Just rf} $ do
                        se :: SExpr <- free_
                        constrain $ se .== e
                        constrain $ fun se ./= v
                        query $ do cs <- checkSat
                                   case cs of
                                     Unsat{} -> io $ appendFile rf "All good.\n"
                                     _       -> error $ "Unexpected: " ++ show cs

evalCheckSL :: ([SExpr] -> SInteger) -> ([SExpr], Integer) -> FilePath -> IO ()
evalCheckSL fun (e, v) rf = runSMTWith z3{verbose=True, redirectVerbose = Just rf} $ do
                        ses :: [SExpr] <- mapM (const free_) e
                        constrain $ ses .== e
                        constrain $ fun ses ./= literal v
                        query $ do cs <- checkSat
                                   case cs of
                                     Unsat{} -> io $ appendFile rf "All good.\n"
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

         Val i     | i .<  10                                -> 3
                   | i .== 10                                -> 4
                   | i .>  10                                -> 5

         _                                                   -> 6
      |]

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

g :: SExpr -> SInteger
g e = [sCase|Expr e of
         Var s     | s .== literal "a"                       -> 0
                   | s .== literal "b" .|| s .== literal "c" -> 1
                   | sTrue                                   -> 2

         Val i     | i .<  10                                -> 3
                   | i .== 10                                -> 4
                   | i .>  10                                -> 5

         Add _ _ -> 6
         Mul _ _ -> 7
         Let{}   -> 8

         _ -> 100
      |]

-- Show that g can never produce anything but 0..8
tSat :: Integer -> FilePath -> IO ()
tSat i rf = runSMTWith z3{verbose=True, redirectVerbose = Just rf} $ do
              a :: SExpr <- free "a"
              constrain $ g a .== literal i

              query $ do cs <- checkSat
                         case cs of
                           Sat{} -> do v <- getValue a
                                       io $ do appendFile rf $ "\nGot: " ++ show v
                                               appendFile rf   "\nDONE\n"
                           Unsat -> io $ do appendFile rf "\nUNSAT\n"
                           _     -> error $ "Unexpected: " ++ show cs

t :: SA -> SA
t = smtFunction "t" $ \a ->
       [sCase|A a of
         A u     -> sA (u+1)
         B w     -> sB (w+2)
         C a1 a2 -> sC (t a1) (t a2)
      |]

-- | A simplifier that uses nested patterns to special-case identity/zero elements.
-- Add (Val 0) e  => e
-- Add e (Val 0)  => e
-- Mul (Val 1) e  => e
-- Mul e (Val 1)  => e
-- Mul (Val 0) _  => 0
-- otherwise      => identity
h :: SExpr -> SExpr
h e = [sCase|Expr e of
         Add (Val i) r | i .== 0 -> r
         Add l (Val i) | i .== 0 -> l
         Mul (Val i) r | i .== 1 -> r
         Mul l (Val i) | i .== 1 -> l
         Mul (Val i) _ | i .== 0 -> sVal 0
         _                        -> e
      |]

-- | Prove that h preserves evaluation semantics: eval (h e) == eval e for all e.
hPreservesEval :: FilePath -> IO ()
hPreservesEval rf = void $ proveWith z3{verbose=True, redirectVerbose=Just rf} $ do
                      e :: SExpr <- free "e"
                      pure $ eval (h e) .== eval e

-- | Focused proof: h preserves eval specifically when the top-level node is Add.
hPreservesEvalAdd :: FilePath -> IO ()
hPreservesEvalAdd rf = void $ proveWith z3{verbose=True, redirectVerbose=Just rf} $ do
                         e :: SExpr <- free "e"
                         pure $ isAdd e .=> (eval (h e) .== eval e)

-- | Focused proof: h preserves eval specifically when the top-level node is Mul.
hPreservesEvalMul :: FilePath -> IO ()
hPreservesEvalMul rf = void $ proveWith z3{verbose=True, redirectVerbose=Just rf} $ do
                         e :: SExpr <- free "e"
                         pure $ isMul e .=> (eval (h e) .== eval e)

-- | A constant-folder using a deeply nested pattern: recognizes Add (Mul (Val a) (Val b)) (Mul (Val c) (Val d))
-- and folds it to Val (a*b + c*d). All four leaf positions use nested Val patterns simultaneously.
cfold :: SExpr -> SExpr
cfold e = [sCase|Expr e of
             Add (Mul (Val a) (Val b)) (Mul (Val c) (Val d)) -> sVal (a*b + c*d)
             _                                               -> e
          |]

-- | Prove that cfold preserves evaluation semantics: eval (cfold e) == eval e for all e.
cfoldPreservesEval :: FilePath -> IO ()
cfoldPreservesEval rf = void $ proveWith z3{verbose=True, redirectVerbose=Just rf} $ do
                          e :: SExpr <- free "e"
                          pure $ eval (cfold e) .== eval e

-- | Prove that the cfold-after-h pipeline preserves evaluation semantics.
cfoldAfterHPreservesEval :: FilePath -> IO ()
cfoldAfterHPreservesEval rf = void $ proveWith z3{verbose=True, redirectVerbose=Just rf} $ do
                                e :: SExpr <- free "e"
                                pure $ eval (cfold (h e)) .== eval e

-- | A function using literal patterns: dispatches on specific integer/string values directly in the pattern.
-- Val 0         => 100
-- Val 1         => 200
-- Add (Val 0) r => eval r   (nested integer literal)
-- _             => eval e   (fallthrough)
p :: SExpr -> SInteger
p e = [sCase|Expr e of
         Val 0         -> 100
         Val 1         -> 200
         Add (Val 0) r -> eval r
         _             -> eval e
      |]
