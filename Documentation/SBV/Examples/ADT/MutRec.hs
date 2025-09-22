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

{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.ADT.MutRec where

import Data.SBV

data A = A1
       | A2 B

data B = B1
       | B2 A

mkSymbolic ''A
mkSymbolic ''B

{-
data Expr var val = Con val
                  | Var var
                  | Add (Expr var val) (Expr var val)
                  | Mul (Expr var val) (Expr var val)
                  | Let (Decl var val) (Expr var val)

data Decl var val = Assign var (Expr var val)
                  | Seq    (Decl var val) (Decl var val)

mkSymbolic ''Decl
mkSymbolic ''Expr
-}
