-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.ADT.PExpr
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing ADTs, parameterized expressions
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.ADT.PExpr(tests) where

import Data.SBV
import Data.SBV.Control
import Utils.SBVTestFramework

import Documentation.SBV.Examples.ADT.Param

-- Testing constructor/type name conflct
data A = A Integer
       | B Word8
       | C A A
       deriving Show

mkSymbolic [''A]

tests :: TestTree
tests =
  testGroup "ADT" [
      goldenCapturedIO "adt_pexpr00c" $ evalCheck  (eval e00,  3)
    , goldenCapturedIO "adt_pexpr00"  $ evalCheckS eval (e00,  3)

    , goldenCapturedIO "adt_pexpr01c" $ evalCheck  (eval e01,  7)
    , goldenCapturedIO "adt_pexpr01"  $ evalCheckS eval (e01,  7)

    , goldenCapturedIO "adt_pexpr02c" $ evalCheck  (eval e02, 21)
    , goldenCapturedIO "adt_pexpr02"  $ evalCheckS eval (e02, 21)

    , goldenCapturedIO "adt_pexpr03c" $ evalCheck  (eval e03, 28)
    , goldenCapturedIO "adt_pexpr03"  $ evalCheckS eval (e03, 28)

    , goldenCapturedIO "adt_pexpr04" $ evalTest  (eval e04)
    , goldenCapturedIO "adt_pexpr05" $ evalTest  (eval e05)

    , goldenCapturedIO "adt_pexpr06c" $ evalCheck  (f (sVar (literal "a")), 0)
    , goldenCapturedIO "adt_pexpr06"  $ evalCheckS f  (sVar (literal "a") , 0)

    , goldenCapturedIO "adt_pexpr07c" $ evalCheck  (f (sVar (literal "b")), 1)
    , goldenCapturedIO "adt_pexpr07"  $ evalCheckS f  (sVar (literal "b") , 1)

    , goldenCapturedIO "adt_pexpr08c" $ evalCheck  (f (sVar (literal "c")), 1)
    , goldenCapturedIO "adt_pexpr08"  $ evalCheckS f  (sVar (literal "c") , 1)

    , goldenCapturedIO "adt_pexpr09c" $ evalCheck  (f (sVar (literal "d")), 2)
    , goldenCapturedIO "adt_pexpr09"  $ evalCheckS f  (sVar (literal "d") , 2)

    , goldenCapturedIO "adt_pexpr10c" $ evalCheck   (sum (map (f . sVal . literal) [-5 .. 9]),  45)
    , goldenCapturedIO "adt_pexpr10"  $ evalCheckSL (sum . map f) ((map (sVal . literal) [-5 .. 9]),  45)

    , goldenCapturedIO "adt_pexpr11c" $ evalCheck   (sum (map (f . sVal . literal) [10, 10]),    8)
    , goldenCapturedIO "adt_pexpr11"  $ evalCheckSL (sum . map f) ((map (sVal . literal) [10, 10]),    8)

    , goldenCapturedIO "adt_pexpr12c" $ evalCheck   (sum (map (f . sVal . literal) [11 .. 20]), 50)
    , goldenCapturedIO "adt_pexpr12"  $ evalCheckSL (sum . map f) ((map (sVal . literal) [11 .. 20]), 50)

    , goldenCapturedIO "adt_pexpr13c" $ evalCheck  (f e00, 3)
    , goldenCapturedIO "adt_pexpr13"  $ evalCheckS f (e00, 3)

    , goldenCapturedIO "adt_pexpr14c" $ evalCheck  (f e01, 6)
    , goldenCapturedIO "adt_pexpr14"  $ evalCheckS f (e01, 6)

    , goldenCapturedIO "adt_pexpr15c" $ evalCheck  (f e02, 6)
    , goldenCapturedIO "adt_pexpr15"  $ evalCheckS f (e02, 6)

    , goldenCapturedIO "adt_pexpr16c" $ evalCheck  (f e03, 6)
    , goldenCapturedIO "adt_pexpr16"  $ evalCheckS f (e03, 6)

    , goldenCapturedIO "adt_pexpr17c" $ evalCheck  (f e04, 6)
    , goldenCapturedIO "adt_pexpr17"  $ evalCheckS f (e04, 6)

    , goldenCapturedIO "adt_pexpr18c" $ evalCheck  (f e05, 6)
    , goldenCapturedIO "adt_pexpr18"  $ evalCheckS f (e05, 6)

    , goldenCapturedIO "adt_pgen00"  t00
    , goldenCapturedIO "adt_pgen01"  $ tSat (-1)
    , goldenCapturedIO "adt_pgen02"  $ tSat 0
    , goldenCapturedIO "adt_pgen03"  $ tSat 1
    , goldenCapturedIO "adt_pgen04"  $ tSat 2
    , goldenCapturedIO "adt_pgen05"  $ tSat 3
    , goldenCapturedIO "adt_pgen06"  $ tSat 4
    , goldenCapturedIO "adt_pgen07"  $ tSat 5
    , goldenCapturedIO "adt_pgen08"  $ tSat 6
    , goldenCapturedIO "adt_pgen09"  $ tSat 7
    , goldenCapturedIO "adt_pgen10"  $ tSat 8
    , goldenCapturedIO "adt_pgen11"  $ tSat 9
    , goldenCapturedIO "adt_pgen12"  $ tSat 100
    , goldenCapturedIO "adt_pchk01"  $ evalTest (t (sA 12))
    ]
    where a = literal "a"
          b = literal "a"

          e00, e01, e02, e03, e04, e05 :: SExpr String Integer
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

evalCheckS :: (SExpr String Integer -> SInteger) -> (SExpr String Integer , Integer) -> FilePath -> IO ()
evalCheckS fun (e, v) rf = runSMTWith z3{verbose=True, redirectVerbose = Just rf} $ do
                        se :: SExpr String Integer <- free_
                        constrain $ se .== e
                        constrain $ fun se ./= literal v
                        query $ do cs <- checkSat
                                   case cs of
                                     Unsat{} -> io $ appendFile rf "All good.\n"
                                     _       -> error $ "Unexpected: " ++ show cs

evalCheckSL :: ([SExpr String Integer] -> SInteger) -> ([SExpr String Integer], Integer) -> FilePath -> IO ()
evalCheckSL fun (e, v) rf = runSMTWith z3{verbose=True, redirectVerbose = Just rf} $ do
                        ses :: [SExpr String Integer] <- mapM (const free_) e
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

f :: SExpr String Integer -> SInteger
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
            a :: SExpr String Word16 <- free "a"
            constrain $ isValid isId a
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

g :: (SymVal val, OrdSymbolic (SBV val), Num (SBV val)) => SExpr String val -> SInteger
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
              a :: SExpr String Word16 <- free "a"
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
