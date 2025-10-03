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
import qualified Data.SBV.List  as SL
import qualified Data.SBV.Tuple as ST

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

exPgm :: FilePath -> Symbolic ()
exPgm rf = do p :: SStmt String Integer <- free "p"

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

tests :: TestTree
tests =
  testGroup "ADT_MR" [
      goldenCapturedIO "adt_mr00" $ r exPgm
    ]
  where r p rf = runSMTWith z3{verbose=True, redirectVerbose = Just rf} (p rf)
