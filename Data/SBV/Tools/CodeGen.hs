-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Tools.CodeGen
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Code-generation from SBV programs.
-----------------------------------------------------------------------------

module Data.SBV.Tools.CodeGen (

        -- * Code generation from symbolic programs
        -- $cCodeGeneration
          SBVCodeGen

        -- ** Setting code-generation options
        , cgPerformRTCs, cgSetDriverValues, cgGenerateDriver, cgGenerateMakefile

        -- ** Designating inputs
        , cgInput, cgInputArr

        -- ** Designating outputs
        , cgOutput, cgOutputArr

        -- ** Designating return values
        , cgReturn, cgReturnArr

        -- ** Code generation with uninterpreted functions
        , cgAddPrototype, cgAddDecl, cgAddLDFlags, cgIgnoreSAssert

        -- ** Code generation with 'SInteger' and 'SReal' types
        -- $unboundedCGen
        , cgIntegerSize, cgSRealType, CgSRealType(..)

        -- ** Compilation to C
        , compileToC, compileToCLib
        , compileToCOpts, compileToCLibOpts
        , CodeGenDisplayOptions(..)
       ) where

import Data.SBV.Compilers.C
import Data.SBV.Compilers.CodeGen

{- $cCodeGeneration
The SBV library can generate straight-line executable code in C. (While other target languages are
certainly possible, currently only C is supported.) The generated code will perform no run-time memory-allocations,
(no calls to @malloc@), so its memory usage can be predicted ahead of time. Also, the functions will execute precisely the
same instructions in all calls, so they have predictable timing properties as well. The generated code
has no loops or jumps, and is typically quite fast. While the generated code can be large due to complete unrolling,
these characteristics make them suitable for use in hard real-time systems, as well as in traditional computing.
-}

{- $unboundedCGen
The types 'SInteger' and 'SReal' are unbounded quantities that have no direct counterparts in the C language. Therefore,
it is not possible to generate standard C code for SBV programs using these types, unless custom libraries are available. To
overcome this, SBV allows the user to explicitly set what the corresponding types should be for these two cases, using
the functions below. Note that while these mappings will produce valid C code, the resulting code will be subject to
overflow/underflows for 'SInteger', and rounding for 'SReal', so there is an implicit loss of precision.

If the user does /not/ specify these mappings, then SBV will
refuse to compile programs that involve these types.
-}
