-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.PseudoBoolean
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Overflow-safe pseudo-Boolean comparisons shared by the C backends.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.PseudoBoolean (assignPseudoBoolean) where

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Core.Data (PBOp(..))

-- | Assign a pseudo-Boolean comparison to an already declared Boolean result.
-- Use an exact unsigned sum when the maximum possible total fits in 64 bits.
-- Otherwise stop adding after exceeding the bound: non-negative coefficients
-- cannot bring the sum back down. Both the bound and each coefficient fit in
-- a signed 64-bit integer, so every addition to a sum at most the bound fits
-- in uint64_t, even when the mathematical total would require more bits.
-- Retain zero-weight operands so their generated bindings remain referenced.
assignPseudoBoolean :: PBOp -> [Doc] -> Doc -> Doc
assignPseudoBoolean operation arguments result
  | length coefficients /= length arguments
  = error "SBV->C: Pseudo-Boolean coefficient/argument count mismatch."
  | any (\n -> n < 0 || n > 2 ^ (63 :: Int) - 1) (bound : coefficients)
  = error "SBV->C: Pseudo-Boolean coefficients and bounds must be non-negative signed 64-bit values."
  | sum coefficients <= 2 ^ (64 :: Int) - 1
  = assign (case terms of [] -> unsigned 0; _ -> parens (hsep (punctuate (text " +") terms)))
  | True
  = text "{"
 $$ nest 2 (text "uint64_t sbv_pb_sum = UINT64_C(0);"
         $$ vcat [ text "if" P.<> parens (accumulator <+> text "<=" <+> unsigned bound <+> text "&&" <+> parens argument)
                $$ nest 2 (accumulator <+> text "+=" <+> unsigned coefficient P.<> semi)
                 | (coefficient, argument) <- weighted
                 ]
         $$ assign accumulator)
 $$ text "}"
 where (coefficients, comparison, bound) = case operation of
         PB_AtMost  k -> (replicate (length arguments) 1, "<=", toInteger k)
         PB_AtLeast k -> (replicate (length arguments) 1, ">=", toInteger k)
         PB_Exactly k -> (replicate (length arguments) 1, "==", toInteger k)
         PB_Le cs   k -> (map toInteger cs,               "<=", toInteger k)
         PB_Ge cs   k -> (map toInteger cs,               ">=", toInteger k)
         PB_Eq cs   k -> (map toInteger cs,               "==", toInteger k)

       weighted      = zip coefficients arguments
       accumulator   = text "sbv_pb_sum"
       unsigned n    = text "UINT64_C" P.<> parens (integer n)
       assign sumDoc = result <+> text "=" <+> sumDoc <+> text comparison <+> unsigned bound P.<> semi
       terms = [parens (argument <+> text "?" <+> unsigned coefficient <+> text ":" <+> unsigned 0)
               | (coefficient, argument) <- weighted]
