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
    ]
    where a = literal "a"
          b = literal "a"

          e00 = 3                                -- 3
          e01 = 3 + 4                            -- 7
          e02 = e00 * e01                        -- 21
          e03 = sLet a e02 (sVar a + e01)        -- 28
          e04 = e03 + sLet a e03 (sVar a + e01)  -- 28 + 28 + 7 = 63
          e05 = sLet b e04 (sVar b * sVar b)     -- 63 * 63 = 3969

evalCheck :: SymVal a => (SBV a, a) -> FilePath -> IO ()
evalCheck (sv, v) rf = runSMTWith z3{verbose=True, redirectVerbose = Just rf} $ do
                        constrain $ sv ./= literal v
                        query $ do cs <- checkSat
                                   case cs of
                                     Unsat{} -> io $ appendFile rf "All good.\n"
                                     _       -> error $ "Unexpected: " ++ show cs

evalCheckS :: (SExpr -> SInteger) -> (SExpr, Integer) -> FilePath -> IO ()
evalCheckS fun (e, v) rf = runSMTWith z3{verbose=True, redirectVerbose = Just rf} $ do
                        se :: SExpr <- free_
                        constrain $ se .== e
                        constrain $ fun se ./= literal v
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
