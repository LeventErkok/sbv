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

{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.ADT.MutRec where

import Data.SBV
import Data.SBV.Control

-- | Expression layer
data Expr var val = Con val
                  | Var var
                  | Add (Expr var val) (Expr var val)
                  | Mul (Expr var val) (Expr var val)
                  | Let (Stmt var val) (Expr var val)
                  deriving Show

-- | Statement layer
data Stmt var val = Assign var (Expr var val)
                  | Seq        (Stmt var val) (Stmt var val)
                  deriving Show

mkSymbolic ''Expr
mkSymbolic ''Stmt

-- | Example program.
--
-- >>> exPgm
exPgm :: IO (Stmt String Integer)
exPgm = runSMT $ do p :: SStmt String Integer <- free "p"

                    -- Make sure there are at least three statements
                    constrain $ isSeq p
                    constrain $ isSeq (getSeq_2 p)
                    constrain $ isSeq (getSeq_2 (getSeq_2 p))

                    query $ do cs <- checkSat
                               case cs of
                                 Sat -> getValue p
                                 _   -> error $ "Unexpected result: " ++ show cs
