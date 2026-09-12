-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.Table
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Lowering of finite SBV lookup tables to C arrays.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.Table
  ( tableExpr
  , tableIndexAndBounds
  , tableMustBeLocal
  ) where

import qualified Data.Set as Set

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Compilers.C.Array    (arrayStoredLoad, arrayStoredValue)
import Data.SBV.Compilers.C.BV       (isWideBV, wideBVLookupIndex, wideBVLookupInRange)
import Data.SBV.Compilers.C.GMP      (isExactGMPKind)
import Data.SBV.Compilers.C.Lowering (CLowering(..), CRequirement(..), expressionLowering)
import Data.SBV.Compilers.C.Value    (valueNeedsOwnership)
import Data.SBV.Compilers.CodeGen    (CgConfig(..))
import Data.SBV.Core.Data
import Data.SBV.Core.Kind             (expandKinds)

-- | Lower a finite SBV table lookup. Bounds are checked when requested by the
-- code-generation configuration, and the default value is returned for every
-- out-of-range index. Only the integral index kinds accepted by SBV's
-- 'Data.SBV.select' operation can reach this function.
tableExpr :: CgConfig -> (SV -> Doc) -> Op -> SV -> Maybe CLowering
tableExpr cfg renderSV (LkUp (tableId, indexKind, _, tableLength) index defaultValue) resultSV
  | isArray resultKind
  = let lowering = arrayStoredLoad resultSV selectedValue
    in Just lowering {loweringRequirements = Set.fromList requirements}
  | True
  = Just $ expressionLowering requirements selectedValue
 where renderedIndex   = renderSV index
       renderedDefault = arrayStoredValue resultKind (renderSV defaultValue)
       lookupValue     = text "table" P.<> int tableId P.<> brackets nativeIndex
       selectedValue   = case outOfRange of
                           Just check | cgRTC cfg -> check <+> text "?" <+> renderedDefault <+> text ":" <+> lookupValue
                           _                      -> lookupValue

       resultKind = kindOf resultSV

       requirements =  [CRequiresGMP    | any (isExactGMPKind cfg) touchedKinds]
                    ++ [CRequiresWideBV | any isWideBV touchedKinds]
                    ++ [CRequiresLibBF  | any isFP touchedKinds]
                    ++ [CRequiresLibM   | any isFP touchedKinds]
                    ++ [CRequiresText   | any (`elem` [KChar, KString]) touchedKinds]
                    ++ [CRequiresLists  | any isList touchedKinds]
                    ++ [CRequiresSets   | any isSet touchedKinds]
                    ++ [CRequiresArrays | any isArray touchedKinds]

       touchedKinds = concatMap expandKinds [indexKind, resultKind]

       (nativeIndex, outOfRange) = tableIndexAndBounds cfg indexKind tableLength renderedIndex
tableExpr _ _ _ _ = Nothing

-- | Render a machine index together with its exact out-of-range predicate.
-- Check the original value before narrowing a wide bit-vector or GMP integer;
-- otherwise a large index could alias an in-range table entry.
tableIndexAndBounds :: CgConfig -> Kind -> Int -> Doc -> (Doc, Maybe Doc)
tableIndexAndBounds cfg indexKind tableLength renderedIndex = (nativeIndex, outOfRange)
 where nativeIndex
         | isWideBV indexKind              = wideBVLookupIndex indexKind renderedIndex
         | isExactGMPKind cfg indexKind     = namedCall "mpz_get_ui" [renderedIndex]
         | True                             = renderedIndex

       outOfRange
         | isWideBV indexKind
         = Just $ text "!" P.<> parens (wideBVLookupInRange indexKind tableLength renderedIndex)
         | isExactGMPKind cfg indexKind
         = Just $ text "!" P.<> parens (   namedCall "mpz_sgn" [renderedIndex] <+> text ">= 0"
                                        <+> text "&&"
                                        <+> namedCall "mpz_cmp_ui" [renderedIndex, int tableLength] <+> text "< 0"
                                      )
         | KBool <- indexKind
         = if maximumIndex indexKind >= fromIntegral tableLength
           then Just $ renderedIndex <+> text ">=" <+> int tableLength
           else Nothing
         | isBounded indexKind
         = case (hasSign indexKind, maximumIndex indexKind >= fromIntegral tableLength) of
             (True,  True)  -> Just . parens $ renderedIndex <+> text "< 0"
                                             <+> text "||"
                                             <+> renderedIndex <+> text ">=" <+> int tableLength
             (True,  False) -> Just $ renderedIndex <+> text "< 0"
             (False, True)  -> Just $ renderedIndex <+> text ">=" <+> int tableLength
             (False, False) -> Nothing
         | KUnbounded <- indexKind
         = case cgInteger cfg of
             Nothing    -> error "SBV->C: Internal error: exact SInteger table index escaped GMP lowering."
             Just width -> case maximumSignedIndex width >= fromIntegral tableLength of
                             True  -> Just . parens $ renderedIndex <+> text "< 0"
                                                     <+> text "||"
                                                     <+> renderedIndex <+> text ">=" <+> int tableLength
                             False -> Just $ renderedIndex <+> text "< 0"
         | True
         = error $ "SBV->C: Unsupported table index kind: " ++ show indexKind

       maximumIndex :: Kind -> Integer
       maximumIndex KBool = 1
       maximumIndex kind
         | hasSign kind = maximumSignedIndex (intSizeOf kind)
         | True         = 2 ^ intSizeOf kind - 1

       maximumSignedIndex :: Int -> Integer
       maximumSignedIndex width = 2 ^ (width - 1) - 1

       namedCall functionName args = text functionName P.<> parens (fsep (punctuate comma args))

-- | Test whether a table declaration must be emitted inside the generated
-- function. Exact GMP values use the function's ownership arena, while
-- managed descriptors point at compound-literal backing storage that is not
-- a portable static C initializer. ADTs are conservatively local because
-- their concrete ownership graph is resolved by the ADT lowering phase.
tableMustBeLocal :: CgConfig -> Kind -> Bool
tableMustBeLocal cfg = any mustBeLocal . expandKinds
 where mustBeLocal kind = isExactGMPKind cfg kind || valueNeedsOwnership cfg kind || isConcreteADT kind

       isConcreteADT kind = isADT kind && not (isRoundingMode kind) && not (isUninterpreted kind)
