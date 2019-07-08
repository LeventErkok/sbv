-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.SMT.SMTLibNames
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- SMTLib Reserved names
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.SMT.SMTLibNames where

import Data.Char (toLower)

-- | Names reserved by SMTLib. This list is current as of Dec 6 2015; but of course
-- there's no guarantee it'll stay that way.
smtLibReservedNames :: [String]
smtLibReservedNames = map (map toLower)
                        [ "Int", "Real", "List", "Array", "Bool", "FP", "FloatingPoint", "fp", "String"
                        , "!", "_", "as", "BINARY", "DECIMAL", "exists", "HEXADECIMAL", "forall", "let", "NUMERAL", "par", "STRING", "CHAR"
                        , "assert", "check-sat", "check-sat-assuming", "declare-const", "declare-fun", "declare-sort", "define-fun", "define-fun-rec"
                        , "define-sort", "echo", "exit", "get-assertions", "get-assignment", "get-info", "get-model", "get-option", "get-proof", "get-unsat-assumptions"
                        , "get-unsat-core", "get-value", "pop", "push", "reset", "reset-assertions", "set-info", "set-logic", "set-option", "match"
                        --
                        -- The following are most likely Z3 specific
                        , "interval", "assert-soft"
                        ]
