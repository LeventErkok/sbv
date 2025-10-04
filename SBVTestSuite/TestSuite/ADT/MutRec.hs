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

import Data.SBV.RegExp
import Data.SBV.Tuple
import Data.SBV.Maybe
import qualified Data.SBV.List  as SL
import qualified Data.SBV.Tuple as ST

-- | Expression layer
data Expr var val = Con { con :: val }
                  | Var { var :: var }
                  | Add { add1 :: Expr var val, add2 :: Expr var val }
                  | Mul { mul1 :: Expr var val, mul2 :: Expr var val }

-- | Statement layer
data Stmt var val = Assign {lhs  :: var,          rhs  :: Expr var val }
                  | Seq    {seqH :: Stmt var val, seqT :: Stmt var val }

mkSymbolic [''Expr, ''Stmt]

data A a b = Aa   { aa :: a }
           | Ab   { ab :: b }
           | Aab  { aba :: a, abb :: b }
           | A2   { a2 :: A b String }
           | A3   { a3 :: A b a }
           deriving Show

mkSymbolic [''A]

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

tests :: TestTree
tests =
  testGroup "ADT_MR" [
      goldenCapturedIO "adt_mr00" $ r t00
    , goldenCapturedIO "adt_mr01" $ r t01
    , goldenCapturedIO "adt_mr02" $ r t02
    , goldenCapturedIO "adt_mr03" $ r t03
    , goldenCapturedIO "adt_mr04" $ r t04
    ]
  where r p rf = runSMTWith z3{verbose=True, redirectVerbose = Just rf} (p rf)

t00 :: FilePath -> Symbolic ()
t00 rf = do p :: SStmt String Integer <- free "p"

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
            constrain $ isValid (sAssign (literal "a") (sCon (literal 1)) :: SStmt String Float)

            query $ do cs <- checkSat
                       case cs of
                         Sat -> do r <- getValue p
                                   io $ do appendFile rf $ "\nGot:\n" ++ show r
                                           appendFile rf   "\nDONE\n"
                         _   -> error $ "Unexpected result: " ++ show cs

t01 :: FilePath -> Symbolic ()
t01 rf = do p :: SStmt String (Maybe (Either Integer Bool)) <- free "p"

            constrain $ isAssign  p
            constrain $ isAdd     (srhs p)
            constrain $ isCon     (sadd1 (srhs p))
            constrain $ isCon     (sadd2 (srhs p))
            constrain $ isNothing (scon (sadd1 (srhs p)))
            constrain $ isJust    (scon (sadd2 (srhs p)))

            query $ do cs <- checkSat
                       case cs of
                         Sat -> do r <- getValue p
                                   io $ do appendFile rf $ "\nGot:\n" ++ show r
                                           appendFile rf   "\nDONE\n"
                         _   -> error $ "Unexpected result: " ++ show cs

t02 :: FilePath -> Symbolic ()
t02 rf = do p :: SA Integer Bool <- free "p"

            constrain $ isA2 p
            constrain $ isA2 (sa2 p)
            constrain $ isAa (sa2 (sa2 p))

            query $ do cs <- checkSat
                       case cs of
                         Sat -> do r <- getValue p
                                   io $ do appendFile rf $ "\nGot:\n" ++ show r
                                           appendFile rf   "\nDONE\n"
                         _   -> error $ "Unexpected result: " ++ show cs

t03 :: FilePath -> Symbolic ()
t03 rf = do p :: SA Integer Bool <- free "p"

            constrain $ isA3 p
            constrain $ isAb (sa3 p)

            query $ do cs <- checkSat
                       case cs of
                         Sat -> do r <- getValue p
                                   io $ do appendFile rf $ "\nGot:\n" ++ show r
                                           appendFile rf   "\nDONE\n"
                         _   -> error $ "Unexpected result: " ++ show cs

t04 :: FilePath -> Symbolic ()
t04 rf = do p :: SA Integer (A Float Bool) <- free "p"

            constrain $ isA2 p
            constrain $ isA3 (sa2 p)
            constrain $ isAab (sa3 (sa2 p))

            query $ do cs <- checkSat
                       case cs of
                         Sat -> do r <- getValue p
                                   io $ do appendFile rf $ "\nGot:\n" ++ show r
                                           appendFile rf   "\nDONE\n"
                         _   -> error $ "Unexpected result: " ++ show cs

_unused :: a
_unused = undefined con var add1 add2 mul1 mul2 lhs rhs seqH seqT
