-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.ADT.MutRec
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Examples of symbolic ADTs referring to each other.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.ADT.MutRec where

import Data.SBV
import Data.SBV.Control

-- import Data.Proxy

-- | Expression layer
data Expr var val = Con val
                  | Var var
                  | Add (Expr var val) (Expr var val)
                  | Mul (Expr var val) (Expr var val)
                  | Let (Stmt var val) (Expr var val)

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
  show (Let a b) = show a ++ "\n" ++ show b

-- | Show instance for 'Stmt'.
instance (Show var, Show val) => Show (Stmt var val) where
  show (Assign v e) = show v ++ " := " ++ show e
  show (Seq a b)    = show a ++ ";\n" ++ show b

-- | Show instance for 'Stmt' specialized when var is string.
instance {-# OVERLAPPING #-} Show val => Show (Stmt String val) where
  show (Assign v e) =      v ++ " := " ++ show e
  show (Seq a b)    = show a ++ ";\n" ++ show b

-- | Example program.
--
-- >>> exPgm
-- !1! := 3;
-- !3! := 5;
-- !2! := 4;
-- !0! := 2
exPgm :: IO (Stmt String Integer)
exPgm = runSMTWith z3{verbose=True} $ do
                    p :: SStmt String Integer <- free "p"

                    -- registerType (Proxy @(Stmt Integer Integer))
                    -- registerType (Proxy @(Expr Integer Integer))

                    -- Make sure there are at least three statements
                    constrain $ isSeq p
                    constrain $ isSeq (getSeq_2 p)
                    constrain $ isSeq (getSeq_2 (getSeq_2 p))

                    query $ do cs <- checkSat
                               case cs of
                                 Sat -> getValue p
                                 _   -> error $ "Unexpected result: " ++ show cs
