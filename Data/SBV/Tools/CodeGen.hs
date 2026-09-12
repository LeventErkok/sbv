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

== Public C names

Function, library, input, and output names must be portable ASCII C identifiers.
Invalid names and C keywords are rejected, not silently renamed. Leading
underscores, @sbv_@ and @SBV@ prefixes, generated type names, and names reserved
for the runtime's C, GMP, and LibBF headers are unavailable for public names.
For example, @my-function@, @switch@, and @sbv_bv_s16_mul@ are rejected.
Ordinary library function names such as @remainder@ are allowed as parameter
names, but not as generated entry points.

Accepted names are preserved in public headers. Implementations and example
drivers use private parameter bindings, so an input named @s0@ cannot collide
with a symbolic temporary, and @values_data@ cannot collide with storage for
an input named @values@. Driver output labels retain the requested names.
Library component files must also have distinct names ignoring ASCII case,
so a bundle is safe to render on case-insensitive filesystems.

User-supplied C prototypes, declarations, and external implementations remain
the caller's responsibility; their identifiers must not conflict with the
generated runtime or entry points.

== Representations and execution

Generated code evaluates the symbolic computation without an SMT solver.
Standalone programs and multi-function static libraries share these mappings:

* Booleans use C @bool@. Native-width bit-vectors use fixed-width C integers;
  other widths use generated limb structures. Arithmetic, shifts, joins, and
  extractions preserve the declared bit width; 673 bits is only one example.
* 'Data.SBV.SInteger', rational-valued 'Data.SBV.SReal', and
  'Data.SBV.SRational' use GMP unless an applicable native mapping is selected.
* 'Data.SBV.SFloat' and 'Data.SBV.SDouble' use native C values. Arbitrary
  floating-point formats and explicitly directed native rounding use LibBF.
  Arbitrary formats are subject to LibBF's exponent-range limits: the backend
  accepts at most 61 exponent bits and checks the selected C LibBF build too.
* Strings and lists use length-aware descriptors. Sets use finite/cofinite
  descriptors. Tuples and concrete ADTs use generated structures, including
  tagged constructors and managed storage for recursive ADTs.
* Symbolic arrays use persistent descriptors supporting constant arrays,
  writes, retained lambdas, and caller-provided lookup callbacks. They are
  distinct from finite lookup tables and 'cgInputArr'/'cgOutputArr' groups.

Generated headers supply ownership helpers for managed values. Inputs borrow
their storage for the call; owned outputs must be released with the appropriate
generated helper. Escaping callback contexts additionally require retain and
release callbacks. See each generated header for its representation contract.

'Data.SBV.smtFunction' definitions and firstified higher-order specializations
can compile to private C functions, including recursive definitions. Explicit
closure environments remain SBV values; this is not an ABI for runtime Haskell
function values. Hard constraints become executable preconditions.

== Runtime failures

Generated programs and libraries use a fail-fast contract: a detected runtime
failure terminates the calling process, using @abort@ or an unsuccessful exit.
This includes failed executable preconditions and enabled assertions, detected
invalid descriptors or missing required callback hooks, and allocation or
resource-limit failures. There is no recoverable status-returning API.

Callers must still satisfy the generated header's ABI and ownership requirements;
runtime checks cannot validate arbitrary pointers or detect every malformed
value. Outputs and cleanup are not guaranteed after failure. Intercepting
termination or using @longjmp@ is not a supported recovery mechanism.

Ordinary numerical results, including floating-point NaNs and infinities and
SBV-defined totalized operations, are not themselves runtime failures.

== Boundaries

General extensional array equality and regular-expression operations are not
implemented. Quantifiers, special solver relations, uninterpreted sorts, and
soft constraints are also rejected. Finite-domain array equality and regex
matching are possible future extensions, not inherently solver-only tasks.

Exact GMP reals represent rational values, not arbitrary algebraic or
transcendental values. Select 'cgSRealType' for native approximations and
@libm@ transcendental operations when rounding is acceptable. The fixed-size
input/output/return group APIs require at least one element; symbolic lists
can be empty.
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
