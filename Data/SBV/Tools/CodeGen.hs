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
        , cgPerformRTCs, cgSetDriverValues, cgArrayEqualityLimit, cgRegexLimits, cgGenerateDriver, cgGenerateMakefile, cgOverwriteFiles, cgShowU8UsingHex
        , CgRegexLimits(..), defaultCgRegexLimits, cgSetRegexLimits

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
The SBV library can generate executable C code from symbolic programs. Total
native bit-vector arithmetic retains compact straight-line code. Programs
using arbitrary-width bit-vectors, arbitrary floating-point values, or exact
numbers can additionally contain generated runtime helpers, loops, and managed
temporary storage appropriate to those representations.

The original, native-scalar-only implementation remains available from
"Data.SBV.Tools.CodeGen.Legacy" for compatibility during the transition to the
new backend.

Migration changes: without an explicit mapping, 'Data.SBV.SInteger' and
rational-valued 'Data.SBV.SReal' now use exact GMP storage and require GMP at
C build time. Legacy rejects these types without 'cgIntegerSize' or
'cgSRealType'. Retain those settings if native, precision-losing mappings are
intentional, or use the Legacy import to retain the original backend.

== Building generated code

'compileToC' writes a function source and header, plus an example driver and
Makefile by default. 'compileToCLib' writes component sources, a shared header,
and a Makefile building @name.a@ (not @libname.a@), with an optional combined
driver. Generated C does not need the Haskell runtime or an SMT solver.

For a standalone function named @example@, a typical build is:

@
make CC=clang CCFLAGS='-std=c11 -Wall -O2'
./example_driver
@

Use 'cgGenerateDriver' to omit the example driver, and 'cgGenerateMakefile' to
integrate sources into an existing build. With the driver disabled, build
@example.o@ for a standalone function or @name.a@ for a library. Example drivers
illustrate the generated calling convention; they are not exhaustive tests.

Dependencies are selected from the operations and representations actually
used, including those inside private functions and array lambdas:

* Native and arbitrary-width bit-vectors, text, collections, arrays, and regex
  matching do not themselves require an external runtime library. Their element
  types or computations can still require one.
* Exact integers, rational reals, and rationals require the C GMP headers and
  library. Generated Makefiles obtain @GMP_CFLAGS@ and @GMP_LIBS@ from
  @pkg-config@; set both variables explicitly if GMP is installed elsewhere.
* LibBF-backed floating-point operations require @libbf.h@ and a compatible C
  LibBF library. The default link flags are @-lbf -lm@. Installing the Haskell
  @libBF@ package does not necessarily install a standalone library named
  @libbf@ on the C linker's search path.
* Native mathematical operations can require @-lm@ without GMP or LibBF.

Generated Makefiles use @CCFLAGS@, not @CFLAGS@, and include local @*.mk@ files
for overrides. Supply nonstandard include paths through @CCFLAGS@ and library
paths through @LDFLAGS@. Required dependencies and 'cgAddLDFlags' are retained
separately in @SBV_LIBS@, so inherited @LDFLAGS@ cannot discard them. Override
@SBV_LIBS@ only to replace dependency discovery; retain every required library.
For example, a LibBF-only program can use:

@
make CC=clang CCFLAGS='-std=c11 -Wall -O2 -I\/path\/to\/libbf' \\
     SBV_LIBS='\/path\/to\/libbf.a -lm'
@

An external C caller should include the generated header and link the generated
object or archive, followed by its required libraries. Static archives do not
embed their GMP or LibBF dependencies. For a dependency-free library named
@example@, for instance:

@
clang -std=c11 -O2 -ffp-contract=off caller.c example.a -o caller
@

Use the generated Makefile's link flags for libraries that need dependencies.
Custom builds must also follow the floating-point and ownership contracts below.

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

Generated ADT constructor tags and structural declaration guards preserve
case. Structural type names encode component boundaries explicitly; array
names length-prefix both the key and value tags. Use the names in the generated
header rather than deriving them from Haskell type spellings.

== Representations and execution

Generated code evaluates the symbolic computation without an SMT solver.
Standalone programs and multi-function static libraries share these mappings:

* Booleans use C @bool@. Native-width bit-vectors use fixed-width C integers;
  other widths use generated limb structures. Arithmetic, shifts, joins, and
  extractions preserve the declared bit width; 673 bits is only one example.
* 'Data.SBV.SInteger', rational-valued 'Data.SBV.SReal', and
  'Data.SBV.SRational' use GMP unless an applicable native mapping is selected.
* 'Data.SBV.SFloat' and 'Data.SBV.SDouble' use native C values. Arbitrary
  floating-point formats and explicitly directed native arithmetic rounding
  use LibBF. Numeric casts between IEEE formats, bit-vectors, and exact GMP
  numbers use LibBF too, except when a native conversion is provably exact.
  Casts honor even the default round-to-nearest mode independently of the
  caller's hardware rounding mode.
  Floating-to-bit-vector casts round first, then retain the destination's low
  bits; non-finite inputs produce zero. The latter choices give deterministic
  results where SMT leaves an out-of-range or non-finite conversion unspecified.
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

Entry points, defined functions, and array lambdas preserve the guards of
conditionals and short-circuit Boolean operations. An inactive branch does not
evaluate its partial ADT selectors or function calls. Total bit-vector work may
be shared outside branches; dependencies needed by both alternatives are also
shared. Explicit assertions and hard constraints remain executable checks even
when the generated function has no outputs.

Finite table selection likewise protects unselected entries and unused defaults.
Already available entries use direct C-array lookup; entries that require guarded
evaluation use a switch. Enable 'cgPerformRTCs' to select the default for an
out-of-range index. With checks disabled (the default), callers must guarantee
in-range indices; invalid unchecked indices have no defined result and may
terminate the process. Wide and exact indices are always checked before
narrowing, independently of this option, to avoid aliasing an in-range entry.

=== Floating-point calling convention

Callers must enter generated code with the hardware rounding mode set to
round-to-nearest, ties-to-even: @FE_TONEAREST@ from @<fenv.h>@. This requirement
applies to standalone generated functions and library entry points. Callbacks
and supplied C implementations must preserve this mode, or restore it before
returning to or re-entering generated code.

Generated code does not check, save, change, or restore the hardware rounding
mode. Violating this precondition is unsupported and need not produce a
diagnostic. Ordinary 'Data.SBV.SFloat' and 'Data.SBV.SDouble' RNE arithmetic
therefore stays native, without a rounding-mode guard or a LibBF fallback.
Explicit non-RNE and symbolic SBV rounding modes still use the rounding-aware
adapters; they do not require the caller to change the hardware mode. The
conversion bridges' independence from hardware rounding does not relax the
entry-point precondition.

Compile generated code with settings that preserve IEEE floating-point
semantics; this precondition does not permit fast-math transformations that
discard NaNs, signed zeros, or required rounding steps.
Generated headers reject detectable fast-math and finite-math-only compiler
modes. Generated Makefiles append @-ffp-contract=off@ after user compiler flags
when compiling and linking, so separate SBV operations cannot be silently fused.
Custom build systems must disable implicit contraction as well, including at
LTO link time; source pragmas alone are insufficient with some compiler options.
Explicit 'Data.SBV.fpFMA' remains a fused, single-rounding operation. Other
unsafe floating-point options and caller-enabled flush-to-zero modes remain
unsupported even when the compiler does not provide a detectable macro.

=== Calling and owning generated values

Input storage, including reachable aggregate fields and callback contexts, must
remain valid and unchanged throughout the call. Pointer parameters must address
valid objects; fixed-size groups require the declared number of elements.
Outputs must not overlap other outputs or storage reachable through an input.
In-place calls are not part of the supported ABI.

Fixed-size input groups follow the same per-element borrowing rules as scalar
inputs. In particular, a group of symbolic arrays accepts a C array of the
generated @SBVArrayInput_...@ callback descriptors, not private array-node
pointers. The example driver initializes and releases managed group elements
individually, including their nested exact values and callback contexts.

Scalar GMP output parameters, including each element of a GMP output group,
must be initialized with @mpz_init@ or @mpq_init@ before the call. They can be
reused across calls and must eventually be cleared by the caller. This also
applies to the extra output parameter used for a single exact-number return.

In contrast, managed string, list, set, tuple, ADT, and array output slots receive
fresh owned values. They need no initialization, even when an aggregate contains
GMP fields. Release an old owned value before reusing its slot; the generated
entry point does not release the previous contents. Each output and return is
an independent owner. Plain C assignment does not create another owner: use the
generated clone or retain helper when both copies must survive independently.
Never release borrowed input storage with an ownership helper.

Reading an owned array can return a borrowed managed value. Clone that value
before releasing the array if it must survive. Likewise, the generated
@sbv_array_output_as_input_...@ helper borrows its array owner; it does not retain
it. A callback's returned storage must remain valid while its context is alive.
Callbacks must implement a stable, immutable lookup. When a non-null context
escapes in a result, both retain and release hooks are required; retaining must
preserve the lookup's meaning and give the result an independent lifetime.

'Data.SBV.smtFunction' definitions and firstified higher-order specializations
can compile to private C functions, including recursive definitions. Explicit
closure environments remain SBV values; this is not an ABI for runtime Haskell
function values. Hard constraints become executable preconditions.

Array lambdas must be closed: their bodies may use their index, literal
constants, and local computations, but may not capture outer symbolic values.
The C backend checks every retained callback before generation, including
nested lambdas, table entries/defaults, and rounding-mode operands. Unsupported
captures are rejected explicitly, never replaced with default values or ignored.
This check is conservative even when a retained capture would not be evaluated.
Capturing array environments are deferred; SBV's existing frontend restrictions
on nested and higher-order captures remain unchanged.

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

== Array equality

Array equality enumerates a supported finite key domain and compares values
using SMT object equality: NaNs are equal and signed floating-point zeros are
distinct. It works for constant, updated, lambda-backed, and caller-provided
arrays, stopping at the first mismatch. No backing array is materialized.
Use 'Data.SBV..===' for arrays involving floating-point types; ordinary
'Data.SBV..==' on such arrays is rejected by SBV before C generation.
Lookup callbacks must respect SMT key equality, including returning the same
value for all NaN encodings of a floating-point key.

'cgArrayEqualityLimit' controls the maximum domain size, defaulting to 256
keys per comparison. For example, setting it to 65536 permits 'Data.SBV.SWord16' keys,
at the cost of up to 65,536 lookups in each array. The setting also applies
inside defined functions and array lambdas, independently for each library
component. A zero limit disables exhaustive comparison. This is a generation
setting, not a runtime timeout; lookup and value-comparison costs are additional.
Exceeding the limit reports the required domain size and suggests raising it.
Infinite or unsupported domains and nested array equality remain unsupported
regardless of the limit. These are generation-time diagnostics, not internal
compiler errors, and library preflight rejects the whole bundle before writing
any component files.

Supported key domains are Booleans, bit-vectors, characters, rounding modes,
floating-point formats, and non-recursive tuples and ADTs built from these.
Floating-point enumeration visits bit encodings but compares only one NaN
representative. Large domains require explicit opt-in even when the generated
loop itself is compact.

For example, admit the full 16-bit domain when generating a comparator:

>>> import Data.SBV
>>> import Data.SBV.Internals (compileToC')
>>> :{
let compareArrays = do
      cgArrayEqualityLimit 65536
      left  <- cgInput "left"  :: SBVCodeGen (SArray Word16 Word8)
      right <- cgInput "right" :: SBVCodeGen (SArray Word16 Word8)
      cgReturn (left .== right)
:}

>>> (_, _, generated) <- compileToC' "compareArrays" compareArrays
>>> length (show generated) `seq` pure ()

== Regular expressions

Regex membership compiles to a bounded deterministic automaton: function-local
static tables and an allocation-free C loop. All 'Data.SBV.RegExp.RegExp'
constructors are supported, including complement, intersection, difference,
and nullable repetitions. Matching consumes the entire string, preserves
embedded NULs, and uses SBV's character domain @0..0x2ffff@, including numeric
surrogate values. The normal canonical string-encoding ABI still applies.
Regex language equality and inequality are decided during generation and
produce Boolean constants, not runtime comparisons.

There are no additional packages, generation tools, headers, or linker flags.
Non-regex programs acquire no regex runtime code. Tables are private to each
generated function and work inside defined functions and closed array lambdas.

'cgRegexLimits' bounds compilation independently per regex operation: maximum
explored automaton states (default 1024), expression nodes (4096), and charged
generation work (16000000). Language comparison counts pairs of residual states.
Expression limits also bound literal/list lengths and repetition expansion;
work accounts for traversals, construction, normalization, and state comparisons.
These are conservative implementation budgets, not time or memory guarantees.
They can reject even a regex whose minimal automaton would be small; this
initial implementation does not minimize automata or optimize large repetitions.

Exceeding a budget fails during generation with a diagnostic naming the limit.
No language approximation or fallback matcher is used. Zero in any limit
disables regex compilation; negative limits are invalid. Successful generation
supports inputs of any length, independently of these limits. Each library
component can choose its own limits. Already folded or dead operations need
no regex compilation.

For example, permit a larger automaton when generating a suffix matcher:

>>> import qualified Data.SBV.RegExp as RE
>>> :{
let suffixMatcher = do
      cgRegexLimits 4096 8192 64000000
      input <- cgInput "input" :: SBVCodeGen SString
      cgReturn (input `RE.match` RE.Conc [RE.All, RE.Literal "done"])
:}

>>> (_, _, regexCode) <- compileToC' "suffixMatcher" suffixMatcher
>>> length (show regexCode) `seq` pure ()

== Boundaries

=== Support policy

The following distinctions apply equally to standalone functions and libraries:

* /Supported representations/: arbitrary-width bit-vectors, native and
  arbitrary-format floats, GMP integers and rational-valued reals, text,
  lists, finite\/cofinite sets, tuples, concrete ADTs, and persistent arrays.
  Dependencies and ownership follow the representation descriptions above.
* /Supported with generation budgets/: exhaustive finite-domain array equality
  ('cgArrayEqualityLimit') and regex compilation ('cgRegexLimits'). Exceeding
  a budget reports the relevant setting; raising it does not enable a different
  feature or change semantics. Regex matching has no approximate fallback.
* /Unsupported types/: uninterpreted sorts, including uses nested in supported
  containers. Uninterpreted /functions/ with caller-supplied C implementations
  are a separate, supported mechanism.
* /Unsupported recursive layouts/: recursive ADT references nested inside
  composite constructor fields, such as tuples. Put recursive references in
  direct constructor fields instead; those use the supported pointer layout.
* /Unsupported equality/: nested arrays and general infinite-domain array
  equality, even for sparse constant-plus-write arrays. The same restriction
  applies to implicit element comparisons in collection operations.
* /Unsupported solver requests/: finite or infinite quantifiers, special
  relations, soft constraints, solver options, optimization objectives, and SMT-only constraint
  attributes. Ordinary hard constraints become executable checks, not searches
  for satisfying inputs.
* /Unsupported closures/: array lambdas capturing outer symbolic values.
  Closed array lambdas and firstified higher-order operations with explicit
  'Data.SBV.Closure' environments remain supported. Unsupported implicit
  higher-order captures are rejected by SBV's frontend or by C preflight when
  retained in a defined function; the backend does not add first-class runtime
  functions or general function equality.
* /Unsupported exact real values/: algebraic roots, transcendental operations
  in exact-rational mode, and inexact or interval literals that do not specify
  a single exact value. A native real mapping explicitly opts into approximate
  arithmetic; it does not choose an approximation for an algebraic literal.

These unsupported cases report an explicit diagnostic during generation,
including retained private-function and array-lambda bodies. Validation of an
entire library precedes file output: a rejected component does not leave earlier
components partially written. This is not a filesystem transaction; an I\/O
failure while writing otherwise valid output can still leave files behind.
Already constant-folded or eliminated operations do not require a lowering.
Runtime failures and caller preconditions are separate contracts, described
above; in particular, violating the RNE entry requirement is not diagnosed.

Array comparisons with infinite or unsupported key domains, or values that
themselves contain arrays, are rejected during generation. Comparing arrays
nested inside collections or aggregates is also not implemented. Quantifiers,
special solver relations, uninterpreted sorts, and soft constraints are rejected.
The comparison restriction includes list searches, prefix/suffix checks, and
replacement: these operations compare elements even when their result is not
a Boolean. Arrays may still be transported inside lists and aggregates without
comparing them. Array-containing set elements and array keys are rejected, since
their representations require element or key equality.

Exact GMP reals represent rational values, not arbitrary algebraic or
transcendental values. Select 'cgSRealType' for native approximations and
@libm@ transcendental operations when rounding is acceptable. The fixed-size
input/output/return group APIs require at least one element; symbolic lists
can be empty.

Numeric conversions honor 'cgIntegerSize' and the @CgFloat@/@CgDouble@ real
mappings. Converting a mapped real to an integer still floors; explicitly
rounded floating casts retain their requested rounding mode. @CgLongDouble@
retains native arithmetic and uses representation-aware LibBF bridges to exact
integers, bit-vectors, and native or arbitrary floating-point formats. These
bridges import the full significand and round directly to the destination,
without narrowing through binary64. The target C compiler must provide binary64,
x87 extended, or binary128 @long double@; other formats (including double-double)
receive a compile-time diagnostic when a bridge is needed. Merely selecting
@CgLongDouble@ does not itself require LibBF. Explicit native mappings remain
approximations: compound expressions, including integer numerator\/denominator
conversions in 'Data.SBV.Rational.sRationalToSReal', retain their separate rounding
steps instead of becoming a single exact-rational conversion.
-}

{- $unboundedCGen
The types 'Data.SBV.SInteger' and 'Data.SBV.SReal' are represented exactly by
GMP when no alternative mapping is selected. The functions below retain the
option of mapping them to native C types when a smaller ABI or compatibility
with historical generated code is more important than exactness. Such native
mappings are subject to overflow for 'Data.SBV.SInteger' and rounding for
'Data.SBV.SReal'.

Real-to-integer flooring preserves the mathematical floor of the represented
native real, then retains the low bits selected by 'cgIntegerSize'. This applies
to @CgFloat@, @CgDouble@, and @CgLongDouble@ without an out-of-range C integer
cast. Flooring a non-finite mapped real terminates the process with a diagnostic.

The compatibility backend in "Data.SBV.Tools.CodeGen.Legacy" retains the
original requirement that these mappings be supplied explicitly.
-}
