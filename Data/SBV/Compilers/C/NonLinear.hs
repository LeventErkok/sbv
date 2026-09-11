-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.NonLinear
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Lowering of transcendental real operations and mapped integer powers.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.NonLinear
  ( nonLinearExpr
  , mappedIntegerPowerRuntime
  ) where

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Compilers.C.Lowering (CLowering, CRequirement(..), CStorage(..), expressionLowering)
import Data.SBV.Compilers.CodeGen    (CgConfig(..), CgSRealType(..))
import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic        (NROp(..))

-- | Lower mapped-real transcendental operations and mapped integer
-- exponentiation. Exact integer exponentiation delegates to the GMP lowering
-- stage, while transcendental operations over exact rational reals receive an
-- actionable diagnostic.
nonLinearExpr :: CgConfig -> Op -> [SV] -> Kind -> [Doc] -> Maybe CLowering
nonLinearExpr cfg (NonLinear nonLinearOp) svs resultKind args
  | nonLinearOp == NR_IntPow
  = integerPower
  | resultKind == KReal && all ((== KReal) . kindOf) svs
  = realOperation
  | True
  = unsupported
 where integerPower
         | resultKind == KUnbounded
         , map kindOf svs == [KUnbounded, KUnbounded]
         , [base, powerValue] <- args
         = case cgInteger cfg of
             Nothing    -> Nothing
             Just width -> Just $ expressionLowering CByValue [CRequiresIntegerPower]
                                $ namedCall ("sbv_integer_pow_s" ++ show width) [base, powerValue]
         | True
         = unsupported

       realOperation = case cgReal cfg of
         Nothing       -> error $ "SBV->C: The exact GMP-rational SReal representation cannot represent "
                                ++ nonLinearName nonLinearOp
                                ++ ". Select a native approximation with cgSRealType to compile this operation."
         Just realType -> Just $ expressionLowering CByValue [CRequiresLibM] (renderReal realType)

       renderReal realType = case (nonLinearOp, args) of
         (NR_Pow   , [left, right]) -> namedCall (realFunction realType "pow") [left, right]
         (NR_IntPow, _            ) -> unsupportedDoc
         (_        , [value]       ) -> namedCall (realFunction realType (nonLinearName nonLinearOp)) [value]
         _                         -> unsupportedDoc

       unsupportedDoc = error unsupportedMessage
       unsupported    = error unsupportedMessage

       unsupportedMessage = "SBV->C: Cannot lower " ++ nonLinearName nonLinearOp
                         ++ " with argument kinds " ++ show (map kindOf svs)
                         ++ " and result kind " ++ show resultKind

       namedCall functionName callArgs = text functionName P.<> parens (fsep (punctuate comma callArgs))

       realFunction CgFloat      baseName = baseName ++ "f"
       realFunction CgDouble     baseName = baseName
       realFunction CgLongDouble baseName = baseName ++ "l"

       nonLinearName NR_Sin    = "sin"
       nonLinearName NR_Cos    = "cos"
       nonLinearName NR_Tan    = "tan"
       nonLinearName NR_ASin   = "asin"
       nonLinearName NR_ACos   = "acos"
       nonLinearName NR_ATan   = "atan"
       nonLinearName NR_Sqrt   = "sqrt"
       nonLinearName NR_Sinh   = "sinh"
       nonLinearName NR_Cosh   = "cosh"
       nonLinearName NR_Tanh   = "tanh"
       nonLinearName NR_Exp    = "exp"
       nonLinearName NR_Log    = "log"
       nonLinearName NR_Pow    = "pow"
       nonLinearName NR_IntPow = "integer exponentiation"
nonLinearExpr _ _ _ _ _ = Nothing

-- | Emit modular exponentiation for an explicitly bounded C representation
-- of 'SInteger'. Negative exponents follow SMT-LIB integer-power semantics;
-- nonnegative results wrap through the selected two's-complement width.
mappedIntegerPowerRuntime :: CgConfig -> Doc
mappedIntegerPowerRuntime cfg = case cgInteger cfg of
  Nothing    -> error "SBV->C: Mapped integer-power runtime requested for exact SInteger"
  Just width -> text . unlines $
    [ "static " ++ signedType ++ " " ++ helperName ++ "(" ++ signedType ++ " base, " ++ signedType ++ " exponent)"
    , "{"
    , "  " ++ unsignedType ++ " result_bits = (" ++ unsignedType ++ ") 1, factor_bits, power;"
    , "  " ++ signedType ++ " result;"
    , "  if (exponent < 0) {"
    , "    if (base == 1) return (" ++ signedType ++ ") 1;"
    , "    if (base == -1) return ((" ++ unsignedType ++ ") exponent & (" ++ unsignedType ++ ") 1) != 0 ? (" ++ signedType ++ ") -1 : (" ++ signedType ++ ") 1;"
    , "    return (" ++ signedType ++ ") 0;"
    , "  }"
    , "  memcpy(&factor_bits, &base, sizeof factor_bits); power = (" ++ unsignedType ++ ") exponent;"
    , "  while (power != 0) {"
    , "    if ((power & (" ++ unsignedType ++ ") 1) != 0) result_bits = (" ++ unsignedType ++ ") ((uint64_t) result_bits * (uint64_t) factor_bits);"
    , "    power = (" ++ unsignedType ++ ") (power >> 1);"
    , "    if (power != 0) factor_bits = (" ++ unsignedType ++ ") ((uint64_t) factor_bits * (uint64_t) factor_bits);"
    , "  }"
    , "  memcpy(&result, &result_bits, sizeof result); return result;"
    , "}"
    , ""
    ]
    where signedType   = "SInt"  ++ show width
          unsignedType = "SWord" ++ show width
          helperName   = "sbv_integer_pow_s" ++ show width
