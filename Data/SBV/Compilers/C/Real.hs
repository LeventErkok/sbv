-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.Real
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Safe flooring of native real representations to mapped integers.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.Real (mappedRealFloorWidth, mappedRealFloorCall, mappedRealFloorRuntime) where

import Data.Maybe (mapMaybe)
import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Compilers.CodeGen (CgConfig(..))
import Data.SBV.Core.Data

-- | Identify flooring from an explicitly native real to a mapped integer.
-- Exact GMP representations are handled by their own conversion paths.
mappedRealFloorWidth :: CgConfig -> Op -> Maybe Int
mappedRealFloorWidth cfg (KindCast KReal KUnbounded)
  | Just _ <- cgReal cfg = cgInteger cfg
mappedRealFloorWidth _ _ = Nothing

-- | Call the width-specific helper. Promotion to long double is exact for
-- the native float and double mappings and preserves long-double precision.
mappedRealFloorCall :: Int -> Doc -> Doc
mappedRealFloorCall width value = text (mappedRealFloorName width) P.<> parens value

-- | Emit the helper only when a program actually floors a mapped real.
-- Reduce the magnitude modulo a power of two before any integer cast. Split
-- 64-bit residues into 32-bit halves so even a binary64 long double never
-- needs to represent UINT64_MAX or a rounded signed upper bound.
-- Non-finite real representations have no mathematical floor and fail fast.
mappedRealFloorRuntime :: CgConfig -> [(SV, SBVExpr)] -> Doc
mappedRealFloorRuntime cfg assignments = case mapMaybe (\(_, SBVApp operation _) -> mappedRealFloorWidth cfg operation) assignments of
  []      -> empty
  width:_ -> text . unlines $
    [ "/* Floor native reals, then retain the mapped integer's low bits. */"
    , "static " ++ signedType ++ " " ++ mappedRealFloorName width ++ "(long double value)"
    , "{"
    , "  if (!isfinite(value)) {"
    , "    fputs(\"SBV->C: Cannot floor a non-finite mapped SReal to SInteger.\\n\", stderr);"
    , "    abort();"
    , "  }"
    , "  const long double integral = floorl(value);"
    , "  const long double residue = fmodl(fabsl(integral), 0x1p" ++ show width ++ "L);"
    , "  const uint64_t high = (uint64_t) (residue / 0x1p32L);"
    , "  const uint64_t low = (uint64_t) (residue - (long double) high * 0x1p32L);"
    , "  uint64_t bits = (high << 32) | low;"
    , "  if (signbit(integral)) bits = UINT64_C(0) - bits;"
    , "  const " ++ unsignedType ++ " raw = (" ++ unsignedType ++ ") bits;"
    , "  " ++ signedType ++ " result; memcpy(&result, &raw, sizeof result); return result;"
    , "}"
    , ""
    ]
    where signedType   = "SInt" ++ show width
          unsignedType = "SWord" ++ show width

-- | Name the private helper by its mapped integer width.
mappedRealFloorName :: Int -> String
mappedRealFloorName width = "sbv_real_floor_to_s" ++ show width
