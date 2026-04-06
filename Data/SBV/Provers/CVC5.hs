-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Provers.CVC5
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- The connection to the CVC5 SMT solver
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Provers.CVC5(cvc5) where

import Data.Char (isSpace)

import qualified Data.Text as T

import Data.SBV.Core.Data
import Data.SBV.SMT.SMT

-- | The description of the CVC5 SMT solver
-- The default executable is @\"cvc5\"@, which must be in your path. You can use the @SBV_CVC5@ environment variable to point to the executable on your system.
-- You can use the @SBV_CVC5_OPTIONS@ environment variable to override the options.
cvc5 :: SMTSolver
cvc5 = SMTSolver {
           name         = CVC5
         , executable   = "cvc5"
         , preprocess   = clean
         , options      = const ["--lang", "smt", "--incremental", "--nl-cov"]
         , engine       = standardEngine "SBV_CVC5" "SBV_CVC5_OPTIONS"
         , capabilities = SolverCapabilities {
                                supportsQuantifiers     = True
                              , supportsDefineFun       = True
                              , supportsDistinct        = True
                              , supportsBitVectors      = True
                              , supportsADTs            = True
                              , supportsUnboundedInts   = True
                              , supportsReals           = True  -- Not quite the same capability as Z3; but works more or less..
                              , supportsApproxReals     = False
                              , supportsDeltaSat        = Nothing
                              , supportsIEEE754         = True
                              , supportsSets            = False
                              , supportsOptimization    = False
                              , supportsPseudoBooleans  = False
                              , supportsCustomQueries   = True
                              , supportsGlobalDecls     = True
                              , supportsDataTypes       = True
                              , supportsLambdas         = True
                              , supportsSpecialRels     = False
                              , supportsDirectTesters   = True
                              , supportsFlattenedModels = Nothing
                              }
         }
  where -- CVC5 wants all input on one line
        clean = T.map simpleSpace . noComment

        noComment t
          | T.null t  = T.empty
          | True      = case T.break (== ';') t of
                          (before, rest)
                            | T.null rest -> before
                            | True        -> before <> noComment (T.dropWhile (/= '\n') (T.tail rest))

        simpleSpace c
          | isSpace c = ' '
          | True      = c
