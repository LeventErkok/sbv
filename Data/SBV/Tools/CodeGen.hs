-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.CodeGen
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Code-generation from SBV programs. This module selects the current C
-- backend. Import "Data.SBV.Tools.CodeGen.Legacy" instead to use the original
-- compatibility backend.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.CodeGen (

        -- * Code generation from symbolic programs
        -- $cCodeGeneration
          SBVCodeGen, cgSym

        -- ** Setting code-generation options
        , cgPerformRTCs, cgSetDriverValues, cgGenerateDriver, cgGenerateMakefile, cgOverwriteFiles, cgShowU8UsingHex

        -- ** Designating inputs
        , cgInput, cgInputArr

        -- ** Designating outputs
        , cgOutput, cgOutputArr

        -- ** Designating return values
        , cgReturn, cgReturnArr

        -- ** Code generation with uninterpreted functions
        , cgAddPrototype, cgAddDecl, cgAddLDFlags, cgIgnoreSAssert

        -- ** Code generation with 'Data.SBV.SInteger' and 'Data.SBV.SReal' types
        -- $unboundedCGen
        , cgIntegerSize, cgSRealType, CgSRealType(..)

        -- ** Compilation to C
        , compileToC, compileToCLib
       ) where

import Data.SBV.Compilers.C
import Data.SBV.Compilers.CodeGen

{- $cCodeGeneration
The SBV library can generate executable C code from symbolic programs. Native
scalar programs remain straight-line code with predictable storage. Programs
using arbitrary-width bit-vectors, arbitrary floating-point values, or exact
numbers can additionally contain generated runtime helpers, loops, and managed
temporary storage appropriate to those representations.

The original, native-scalar-only implementation remains available from
"Data.SBV.Tools.CodeGen.Legacy" for compatibility during the transition to the
new backend.
-}

{- $unboundedCGen
The types 'Data.SBV.SInteger' and 'Data.SBV.SReal' are represented exactly by
GMP when no alternative mapping is selected. The functions below retain the
option of mapping them to native C types when a smaller ABI or compatibility
with historical generated code is more important than exactness. Such native
mappings are subject to overflow for 'Data.SBV.SInteger' and rounding for
'Data.SBV.SReal'.

The compatibility backend in "Data.SBV.Tools.CodeGen.Legacy" retains the
original requirement that these mappings be supplied explicitly.
-}
