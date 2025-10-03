-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.ADT.MutRec
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing ADTs, mutual-recursion and other parameterization checks
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.ADT.MutRec(tests) where

import Data.SBV
import Data.SBV.Control
import Utils.SBVTestFramework

import Data.Proxy

-- | Expression layer
data Expr var val = Con val
                  | Var var
                  | Add (Expr var val) (Expr var val)
                  | Mul (Expr var val) (Expr var val)

-- | Statement layer
data Stmt var val = Assign var (Expr var val)
                  | Seq        (Stmt var val) (Stmt var val)

mkSymbolic [''Expr, ''Stmt]

-- | Show instance for 'Expr'.
instance (Show var, Show val) => Show (Expr var val) where
  show (Con i)   = show i
  show (Var a)   = show a
  show (Add l r) = "(" ++ show l ++ " + " ++ show r ++ ")"
  show (Mul l r) = "(" ++ show l ++ " * " ++ show r ++ ")"

-- | Show instance for 'Stmt'.
instance (Show var, Show val) => Show (Stmt var val) where
  show (Assign v e) = show v ++ " := " ++ show e
  show (Seq a b)    = show a ++ ";\n" ++ show b

-- | Show instance for 'Expr' specialized when var is string.
instance {-# OVERLAPPING #-} Show val => Show (Expr String val) where
  show (Con i)   = show i
  show (Var a)   = a
  show (Add l r) = "(" ++ show l ++ " + " ++ show r ++ ")"
  show (Mul l r) = "(" ++ show l ++ " * " ++ show r ++ ")"

-- | Show instance for 'Stmt' specialized when var is string.
instance {-# OVERLAPPING #-} Show val => Show (Stmt String val) where
  show (Assign v e) =      v ++ " := " ++ show e
  show (Seq a b)    = show a ++ ";\n" ++ show b

-- | Validity: We require each variable appearing to be an identifier (lowercase letter followed by
-- any number of upper-lower case letters and digits), and all expressions are closed; i.e., any
-- variable referenced is assigned by a prior assignment expression.
isValid :: forall val. SymVal val => SStmt String val -> SBool
isValid = ST.fst . goS SL.nil
  where isId s = s `match` (asciiLower * KStar (asciiLetter + digit))

        goE :: SList String -> SExpr String val -> SBool
        goE = smtFunction "validE" $ \env expr -> [sCase|Expr expr of
                                                     Con _   -> sTrue
                                                     Var s   -> isId s .&& s `SL.elem` env
                                                     Add l r -> goE env l .&& goE env r
                                                     Mul l r -> goE env l .&& goE env r
                                                  |]

        goS :: SList String -> SStmt String val -> STuple Bool [String]
        goS = smtFunction "validS" $ \env stmt -> [sCase|Stmt stmt of
                                                     Assign v e -> tuple (isId v .&& goE env e, v SL..: env)
                                                     Seq    a b -> let (lv, env')  = untuple $ goS env  a
                                                                       (rv, env'') = untuple $ goS env' b
                                                                   in tuple (lv .&& rv, env'')
                                                  |]

-- | Example program. Note that we do not put the 'isValid' constraint
-- on this example since neither z3 nor cvc5 converges with that constraint in.
-- Hence the bizarre variable names below.
--
-- >>> exPgm
-- !2! := 3;
-- !4! := 5;
-- !3! := 4;
-- !0! := (!1! + 2)
exPgm :: IO (Stmt String Integer)
exPgm = runSMT $ do p :: SStmt String Integer <- free "p"

                    registerType (Proxy @(Expr Integer Integer))

                    -- Make sure there's some structure to the program:
                    constrain $ isSeq    p
                    constrain $ isSeq    (getSeq_2 p)
                    constrain $ isSeq    (getSeq_2 (getSeq_2 p))
                    constrain $ isAssign (getSeq_2 (getSeq_2 (getSeq_2 p)))
                    constrain $ isAdd    (getAssign_2 (getSeq_2 (getSeq_2 (getSeq_2 p))))
                    constrain $ isVar    (getAdd_1    (getAssign_2 (getSeq_2 (getSeq_2 (getSeq_2 p)))))

                    -- Would love to have the following. But it creates too big of a problem.
                    -- constrain $ isValid p

                    query $ do cs <- checkSat
                               case cs of
                                 Sat -> getValue p
                                 _   -> error $ "Unexpected result: " ++ show cs
-- Testing constructor/type name conflct
data A = A Integer
       | B Word8
       | C A A
       deriving Show

mkSymbolic [''A]

tests :: TestTree
tests =
  testGroup "ADT_P" [
      goldenCapturedIO "adt_pexpr00" $ evalCheck (eval e00,  3)
    , goldenCapturedIO "adt_pexpr01" $ evalCheck (eval e01,  7)
    , goldenCapturedIO "adt_pexpr02" $ evalCheck (eval e02, 21)
    , goldenCapturedIO "adt_pexpr03" $ evalCheck (eval e03, 28)
    , goldenCapturedIO "adt_pexpr04" $ evalTest  (eval e04)
    , goldenCapturedIO "adt_pexpr05" $ evalTest  (eval e05)
    , goldenCapturedIO "adt_pexpr06" $ evalCheck (f (sVar (literal "a")), 0)
    , goldenCapturedIO "adt_pexpr07" $ evalCheck (f (sVar (literal "b")), 1)
    , goldenCapturedIO "adt_pexpr08" $ evalCheck (f (sVar (literal "c")), 1)
    , goldenCapturedIO "adt_pexpr09" $ evalCheck (f (sVar (literal "d")), 2)
    , goldenCapturedIO "adt_pexpr10" $ evalCheck (sum (map (f . sVal . literal) [-5 .. 9]),  45)
    , goldenCapturedIO "adt_pexpr11" $ evalCheck (sum (map (f . sVal . literal) [10, 10]),    8)
    , goldenCapturedIO "adt_pexpr12" $ evalCheck (sum (map (f . sVal . literal) [11 .. 20]), 50)
    , goldenCapturedIO "adt_pexpr13" $ evalCheck (f e00, 3)
    , goldenCapturedIO "adt_pexpr14" $ evalCheck (f e01, 6)
    , goldenCapturedIO "adt_pexpr15" $ evalCheck (f e02, 6)
    , goldenCapturedIO "adt_pexpr16" $ evalCheck (f e03, 6)
    , goldenCapturedIO "adt_pexpr17" $ evalCheck (f e04, 6)
    , goldenCapturedIO "adt_pexpr18" $ evalCheck (f e05, 6)
    , goldenCapturedIO "adt_pexpr19" $ satCheck (\(x :: SExpr Integer Word8)    -> isLet x)
    , goldenCapturedIO "adt_pexpr20" $ satCheck (\(x :: SExpr Word8   Rational) -> isMul x)
    , goldenCapturedIO "adt_pexpr21" $ satCheck (\(x :: SExpr (Maybe (Integer, String)) (Either Word8 Int16)) -> isLet x)
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

satCheck :: (Show a, SymVal a, QuantifiedBool b) => (SBV a -> b) -> FilePath -> IO ()
satCheck tst rf = runSMTWith z3{verbose=True, redirectVerbose = Just rf} $ do
                    x <- free "x"
                    constrain $ tst x
                    query $ do cs <- checkSat
                               case cs of
                                 Unsat{} -> io $ appendFile rf "Got unsat\n"
                                 Sat{}   -> do xv <- getValue x
                                               io $ appendFile rf ("Result: " ++ show xv ++ "\n")
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
