* Hackage: <http://hackage.haskell.org/package/sbv>
* GitHub:  <http://github.com/LeventErkok/sbv>

### Version 10.9, 2024-04-05

  * Fix printing of floats to be more consistent, using lowercase letters

### Version 10.8, 2024-04-05

  * Increase the number of digits used in printing floats in decimal base, which leads to
    better output in most cases.

### Version 10.7, 2024-03-23

  * Fix SMTDefinable instances for functions of arity 8-12. Thanks to Nick Lewchenko for the patch.
    
### Version 10.6, 2024-03-16

  * Added Data.SBV.Tools.BVOptimize module, which implements a custom optimizer for unsigned bit-vector
    values. See 'minBV' and 'maxBV' methods. These algorithms use the incremental solver instead of
    the optimizer engines, and they can be more performant in certain cases. (For instance, z3's
    optimization engine isn't incremental, which makes it perform poorly on certain BV-optimization
    problems.) These algorithms scan the bits from most to least significant bit, and individually
    set/unset them in an incremental fashion to optimize quickly.

  * SBV web-page is no longer maintained. The info is put into the README.md instead.

### Version 10.5, 2024-02-20

  * Export svFloatingPointAsSWord through Data.SBV.Internals

  * crackNum: if verbose, alert the user if surface value of a NaN doesn't match its calculated value
    due to the redundancy in NaN representations.

### Version 10.4, 2024-02-15

  * Before issuing a get-value, make sure there are no outstanding assert calls.
    See: https://github.com/LeventErkok/sbv/issues/682 for details.

  * crackNum mode now displays the surface form of NaNs more faithfully, if provided
    with the input string. This functionality is used by the crackNum executable.

### Version 10.3, 2024-01-05

  * Clean-up GHC extensions required in the cabal file, and changes required to compile cleanly with GHC 9.8 series.

  * Added 'partition', which allows for partitioning all-sat search spaces when models are generated.

  * Added 'sSetBitTo', variant of 'setBitTo', but allows symbolic indexes.

  * Added 'uninterpretWithArgs', which allows for user given argument names for uninterpreted functions. These
    names come in handy when displaying models of uninterpreted functions.

  * Added `Documentation.SBV.Examples.Misc.ProgramPaths`, showing an example use of all-sat partitioning.

  * Added `Documentation.SBV.Examples.BitPrecise.PEXT_PDEP`, modeling x86 instructions PDEP and PEXT.

  * Added `Documentation.SBV.Examples.Puzzles.Newspaper`, another puzzle example.

  * Added `Documentation.SBV.Examples.ProofTools.AddHorn`, demonstrating the use of the horn-clause solver for
    invariant generation.

  * Add 'sbv2smt', which renders the given sbv definition as an SMTLib definition. Mainly useful for debugging purposes.
    It can render both ground definitions and functions, and the latter can be handy in producing SMTLib functions to
    be used in other settings.

  * Add support for OpenSMT from Università della Svizzera italiana https://verify.inf.usi.ch/opensmt

  * Fix a bug in bit-vector rotation that manifested itself in small-bv sizes. Thanks to Sirui Lu for reporting.

  * [BACKWARDS COMPATIBILITY] Change the overflow detection API to match the new SMTLib predicates. These predicates
    do not distinguish between over/underflow, so strictly speaking the new API is less powerful than the old one. However,
    we choose to follow SMTLib here for portability purposes. If you need separate overflow/underflow checking you can
    use the encodings from earlier implementations, please get in touch if this proves problematic.

  * [BACKWARDS COMPATIBILITY] Dropped hasSize, which checked cardinality of sets. This call hasn't been supported by
    z3 for some time, and its uses were thus limited, and behavior was problematic even when supported due to finiteness
    issues.

  * Removed a few examples, which were causing regression failures with changes in z3. These are trickier examples, and
    new releases of z3 had varying performance issues, making them not suitable regression and documentation purposes. In
    particular, 'Documentation.SBV.Examples.Existentials.CRCPolynomial', 'Documentation.SBV.Examples.Lists.Nested', and
    'Documentation.SBV.Examples.BitPrecise.MultMask' were removed.

  * SBV now keeps track of contexts, thus avoiding rare (but unsound) cases of incorrect API usage where contexts
    are mixed. We now issue a run-time error. See https://github.com/LeventErkok/sbv/issues/71 for details.

  * Improve the getFunction signature, to return more detailed info on the produced SMT functions, including the parse-tree.

  * SBV now tracks whether a declared uninterpreted function is curried or not. This helps in more precise printing of
    satisfying models with uninterpreted functions. (Previously all UI functions were displayed as if they were curried.)

### Version 10.2, 2023-06-09

  * Improve HLint pragmas. Thanks to George Thomas for the patch.

  * Added an implementation of the Prince encryption algorithm. See Documentation/SBV/Examples/Crypto/Prince.hs.

  * Added on-the-fly decryption mode for AES. See Documentation/SBV/Examples/Crypto/AES.hs for details.

  * Added functions `sEDivMod`, `sEDiv`, and `sEMod` which perform euclidian division over symbolic integers.

  * Added 'Data.SBV.Tools.NaturalInduction' which provides a proof method to perform induction over natural numbers. See the functions 'inductNat' and 'inductNatWith'.

### Version 10.1, 2023-04-14

  * [BACKWARDS COMPATIBILITY] SBV now handles quantifiers in a much more disciplined way. All of the previous
    ways of creating quantified variables (i.e., the functions sbvForall, sbvExists, universal, existential) are
    removed. Instead, we can now express quantifiers in a much straightforward way, by passing them to
    'constrain' directly. A simple example is:

        constrain $ \(Forall x) (Exists y) -> y .> (x :: SInteger)

    You can nest quantifiers as you wish, and the quantified parameters can be of arbitrary symbolic type.
    Additionally, you can convert such a quantified formula to a regular boolean, via a call to 'quantifiedBool'
    function, essentially performing quantifier elimination:

        other_condition .&& quantifiedBool (\(Forall x) (Exists y) -> y .> (x :: SInteger))

    Or you can prove/sat quantified formulas directly:

        prove $ \(Forall x) (Exists y) -> y .> (x :: SInteger)

    This facility makes quantifiers part of the regular SBV language, allowing them to be mixed/matched with all
    your other symbolic computations.

    SBV also supports the constructors ExistsUnique to create unique existentials, in addition to
    ForallN and ExistsN for creating multiple variables at the same time.

    The new function skolemize can be used to skolemize quantified formulas: The skolemized version of a
    formula has no existential (replaced by uninterpeted functions), and is equisatisfiable to the original.

    See the following files demonstrating reasoning with quantifiers:
    
       * Documentation/SBV/Examples/Puzzles/Birthday.hs
       * Documentation/SBV/Examples/Puzzles/KnightsAndKnaves.hs
       * Documentation/SBV/Examples/Puzzles/Rabbits.hs
       * Documentation/SBV/Examples/Misc/FirstOrderLogic.hs

  * You can now define new functions in the generated SMTLib output, via an smtFunction call. Typically, we simply
    unroll all definitions, but there are certain cases where we would like the functions
    remain intact in the output. This is especially true of recursive functions, where the termination would
    depend on a symbolic variable, which cannot be symbolically-simulated. By translating these to SMTLib
    functions, we can now handle such definitions. Note that such definitions will no longer be constant-folded
    on the Haskell side, and each call will induce a call in the solver instead. The new method smtFunction
    can handle both recursive and non-recursive functions. See "Documentation/SBV/Examples/Misc/Definitions.hs"
    for examples.

  * Added new SList functions: map, mapi, foldl, foldr, foldli, foldri, zip, zipWith, filter, all, any.
    Note that these work on arbitrary--but finite--length lists, with all terminating elements, per
    usual SBV interpretation. These functions map to the underlying solver's fold and map functions,
    via lambda-abtractions. Note that the SMT engines remain incomplete with respect to sequence
    theories. (That is, any property that requires induction for its proof will cause unknown
    answers, or will not terminate.) However, basic properties, especially when the solver can determine the
    shape of the sequence arguments (i.e., number of elements), should go through.

  * New function 'lambdaAsArray' allows creation of array values out of lambda-expressions. See
    "Documentation/SBV/Examples/Misc/LambdaArray.hs" for an example use. This adds expressive power,
    as we can now specify arrays with index dependent contents much more easily.

  * Added support for abduct-generation, as supported by CVC5. See "Documentation/SBV/Examples/Queries/Abducts.hs"
    for a basic example.

  * Added support for special-relations. You can now check if a relation is partial, linear, tree,
    or piecewise-linear orders in SBV. (Or you can constrain relations to satisfy the corresponding laws, thus
    creating relations with these properties.) Additionally, you can create transitive-closures of relations.
    See Documentation/SBV/Examples/Misc/FirstOrderLogic.hs for several examples.

  * [BACKWARDS COMPATIBILITY] The signature of Data.SBV.List's concat has changed. In previous releases
    this was a synonym for appending two lists, now it takes a list-of-lists and flattens it, matching the
    Haskell list function with the same name.

  * [BACKWARDS COMPATIBILITY] The function addAxiom is removed. Instead use quantified-constraints, as described
    above.

  * [BACKWARDS COMPATIBILITY] Renamed the Uninterpreted class to SMTDefinable, since its task has changed, handling
    both kinds of definitions. Unless you were referring to the name Uninterpreted in your code, this should not
    impact you. Otherwise, simply rename it to SMTDefinable.

  * [BACKWARDS COMPATIBILITY] The configuration variable 'allowQuantifiedQueries' is removed. It is no
    longer relevant with our new quantification strategy described above.

  * [BACKWARDS COMPATIBILITY] The function 'isVacuous' is renamed to 'isVacuousProof' (and 'isVacuousWith'
    became 'isVacuousProofWith') to better reflect this function applies to checking vacuity in a proof context.

  * [BACKWARDS COMPATIBILITY] Satisfiability and proof checks are now put in different classes, instead of sharing
    the same class. This should not have any impact on user-level code, unless you were building libraries
    on top of SBV. See the 'ProvableM' and 'SatisfiableM' classes.

  * [BACKWARDS COMPATIBILITY] Renamed 'Goal' to 'ConstraintSet' which is more indicative of its purpose. A set
    of constraints can be satisfied, but proving them does not make sense. The name goal, however, suggested
    something we can prove.

  * [BACKWARDS COMPATIBILITY] SBV is now more lenient in returning function-interpretations, returning the SMTLib
    string in complicated cases in case of bailing out. Note that we still don't support complicated function
    values in allSat calls, as there's no way to reject existing interpretations. Consequently, the
    parameter 'satTrackUFs' is renamed to 'allSatTrackUFs' to better capture its new role.

  * Addressed an issue on Windows where solver synchronization fails due to unmapped diagnostic-challenge.
    (See issue #644 for details.) Thanks to Ryan Scott for reporting and helping with debugging.

  * Add missing Arbitrary instances for WordN and IntN types, enabling quickcheck on these types.

  * Rewrote some of the older examples to use more modern SBV idioms.

  * Changes needed to compile with upcoming GHC 9.6. Thanks to Lars Kuhtz and Ryan Scott for several patches.

### Version 9.2, 2023-1-16

  * Handle uninterpreted sorts better, avoiding kind-registration issue.
    See #634 for details. Thanks to Nick Lewchenko for the report.

### Version 9.1, 2023-01-09

  * CVC5: Add support for algebraic reals in CVC5 models

  * Export more solvers from Trans/Dynamic interfaces. Thanks to Ryan Scott for the patch.

### Version 9.0, 2022-04-27

  * Changes required to compile cleanly with GHC 9.2 series.

  * In future versions, GHC will make `forall` a reserved word, which will create a conflict with SBV's use of the same.
    To accommodate for these changes and to be consistent, following identifiers were renamed:

       - `forall`   --> `sbvForall`
       - `forall_`  --> `sbvForall_`
       - `exists`   --> `sbvExists`
       - `exists_`  --> `sbvExists_`
       - `forAll`   --> `universal`
       - `forAll_`  --> `universal_`
       - `forSome`  --> `existential`
       - `forSome_` --> `existential_`

   * Add support for `reverse` on symbolic lists and strings. Note that this definition uses a recursive function
     declaration in SMTLib, so any proof involving inductive reasoning will likely not-terminate. However, it
     should be usable at ground-level and for simpler non-inductive properties. Of course, as SMT-solvers mature
     this can change in the future.

   * Changed the String/List versions of `.++/.!!` to directly use the names `++/!!`. Since these modules
     are intended to be used qualified only, there's no reason to add the dots.

   * Added function `addSMTDefinition`, which allows users to give direct definitions of SMTLib functions. This
     is useful for defining recursive functions that are not symbolically terminating.

   * Added `Documentation.SBV.Examples.Lists.CountOutAndTransfer` example, proving that the so-called
     coating card trick works correctly.

   * Added `Documentation.SBV.Examples.Puzzles.Jugs` example, solving the water-jug transfer puzzle.

   * Added `Documentation.SBV.Examples.Puzzles.AOC_2021_24` example, showing how to model an EDSL in SBV,
     solving the advent-of-code, 2021, day 24 problem.

   * Added `Documentation.SBV.Examples.Puzzles.Drinker` example, proving the famous Drinker paradox of
     Raymond Smullyan.

   * Added concrete type instances of Mergeable class.

   * Fixed a bug in the implementation of the concrete-path for sPopCount
   
   * Added complement, power, and difference operators for regular expressions. Also added `everything`, `nothing`,
     `anyChar` as new recognizers.

   * Fixed the semantics of `All` regular expressions to recognize all-strings, and added `AllChar` as a
     new regular-expression constructor to match any single regular expression. Thanks to Matt Torrence for
     the patch.

   * Fixed a bug in the concrete implementation of bit-vector join, which didn't handle signed quantities
     correctly. Thanks to Sirui Lu for the report and test cases.

### Version 8.17, 2021-10-25

  * SBV now supports cvc5; the latest incarnation of CVC. See https://github.com/cvc5/cvc5
    for details.

  * SBV now supports bitwuzla; the latest incarnation of Boolector. See https://bitwuzla.github.io
    for details.

  * Fixed handling of CRational values in constant folding, which was missing a case.
    Thanks to Jaro Reinders for reporting.

  * Fixed calls to distinct for floating-point values, causing SBV to throw an exception.

  * Add missing instances of SatModel for Char and String. Thanks to eax- on github
    for the contribution.

  * Add support for symbolic comparison of regular expressions.

  * Export svToSV from Data.SBV.Dynamic. Thanks to Matt Parker for the PR.

### Version 8.16, 2021-08-18

  * Put extra annotations on data-type constructors, which makes
    SBV generate problems that z3 can parse more easily. Thanks to
    Greg Sullivan for reporting the issue in the first place.

### Version 8.15, 2021-05-30

  * Remove support for SFunArray abstraction. Turns out that the caching
    mechanisms SBV used for SFunArray weren't entirely safe, and the code
    has become unmaintainable over-time. Instead you should simply use
    SArray, which has the exact same API. Thanks to frenchFrog42 on
    github for reporting some of the problems.

  * Fix the cmd line params for invocations of Boolector. You need
    Boolector 3.2.2 to work with this version of SBV.

  * NB. Recent releases of z3 no longer support optimization of real-valued
    goals in the presence of strict inequalities, i.e., .>, .<, and ./= operators.
    So, you might get a bogus result if you are using optimization with
    SReal parameters that have strict inequalities. See https://github.com/Z3Prover/z3/issues/5314
    for details. There is not much SBV can do to prevent these, unfortunately,
    as z3 optimization engine goals seem to have changed. Note that use of
    non-strict inequalities (i.e., .>=, .<=) should be fine. Also, this
    only impacts the optimize calls: regular sat/prove invocations are not
    impacted.

### Version 8.14, 2021-03-29

  * Improve the fast all-sat algorithm to also support uninterpreted values.

  * Generalize svTestBit to work on floats, returning the respecting bit in the
    representation of the float.

  * Fixes to crack-num facility of how we display floats in detail.

### Version 8.13, 2021-03-21

  * Generalized floating point: Add support for brain-floats, with
    type `SFPBFloat`, which has 8-bits of exponent and 8-bits of
    significand. This format is affectionately called "brain-float"
    because it's often used in modeling neural networks machine-learning
    applications, offering a wider-range than IEEE's half-float, at the
    exponse of reduced precision. It has 8-exponent bits and 8-significand
    bits, including the hidden bit.

  * Add support for SRational type, rational values built out of the ratio
    of two integers. Use the module "Data.SBV.Rational", which exports the
    constructor .% to build rationals. Note that you cannot take numerator
    and denominator of rationals apart, since SMTLib has no way of storing
    the rational in a canonical way. Otherwise, symbolic rationals follow
    the same rules as Haskell's Rational type.

  * SBV now implements a faster allSat algorithm, which applies in most common
    use cases. (Essentially, when there are no uninterpreted values or sorts present.)
    The new algorithm has been measured to be at least an order of magnitude
    faster or more in common cases as it splits the search space into disjoint
    models, reducing the burden of accummulated lemmas over multiple calls. (See
    http://theory.stanford.edu/%7Enikolaj/programmingz3.html#sec-blocking-evaluations
    for details.)

### Version 8.12, 2021-03-09

  * Fix a bug in crackNum for unsigned-integer values, which incorrectly
    showed a negation sign for values with msb set to 1.

### Version 8.11, 2021-03-09

  * SBV now supports floating-point numbers with arbitrary exponent and
    significand sizes. The type is `SFloatingPoint eb sb`, where `eb`
    and `sb` are type-level naturals. In particular, SBV can now reason about
    half-floats, which are used much more frequently in ML applications. Through
    the LibBF binding, you can also use these concretely, so if you have a use
    case for computing with floats, you can use SBV as a vehicle for doing so.
    The exponent/significand sizes are limited to those supported by the LibBF
    bindings, though the allowed range is rather large and should not be a limitation
    in practice. (In particular, you'll most likely run out of memory before you
    hit precision limits!)

  * We now support a separate `crackNum` parameter in model display. If set to True
    (default is False), SBV will display numeric values of bounded integers, words,
    and all floats (SDouble, SFloat, and the new SFloatingPoint) in models in detail,
    showing how they are laid out in memory. Numbers follow the usual 2's-complement
    notation if they are signed, bit-vectors if they are not signed, and the floats
    follow the usual IEEE754 binary layout rules. Similarly, there's now a function
    crack :: SBV a -> String that does the same for non-model printing contexts.

  * Changed the isNonModelVar config param to take a String (instead of Text).
    Simplifies programming.

  * Changes to make SBV compile with GHC9.0. Thanks to Ryan Scott for the patch.

### Version 8.10, 2021-02-13

  * Add "Documentation/SBV/Examples/Misc/NestedArray.hs" to demonstrate how
    to model multi-dimensional arrays in SBV.

  * Add "Documentation/SBV/Examples/Puzzles/Murder.hs" as another puzzle example.

  * Performance updates: Thanks to Jeff Young, SBV now uses better underlying
    data structures, performing better for heavy use-case scenarios.

  * SBV now tracks constants more closely in query mode, providing more support
    for constant arrays in a seamless way. (See #574 for details.)

  * Pop-calls are now supported for Yices and Boolector. (#577)

  * Changes required to make SBV work with latest version of z3 regarding
    String and Characters, which now allow for unicode characters. This required
    renaming of certain recognizers in 'Data.SBV.Char' to restrict them to the
    Latin1 subset. Otherwise, the changes should be transparent to the end user.
    Please report any issues you might run into when you use SChar and SString types.

### Version 8.9, 2020-10-28

  * Rename 'sbvAvailableSolvers' to 'getAvailableSolvers'.

  * Use SMTLib's int2bv if supported by the backend solver. If not, we still
    do a manual translation. (CVC4 and z3 support it natively, Yices and
    MathSAT does not, for which we do the manual translation. ABC and dReal
    doesn't support the coversion at all, since former doesn't support integers
    and the latter doesn't support bit-vectors.) Thanks to Martin Lundfall
    for the initial pull request.

  * Add `sym` as a synonym for `uninterpret`. This allows us to write expressions
    of the form `sat $ sym "a" - sym "b" .== (0::SInteger)`, without resorting to lambda
    expressions or having to explicitly be in the Symbolic monad.

  * Added missing instances for overflow-checking arithmetic of arbitrary
    sized signed and unsigned bitvectors.

  * In a sat (or allSat) call, also return the values of the uninterpreted values, along with
    all the explicitly named inputs. Strictly speaking, this is backwards-incompatible,
    but it the new behavior is consistent with how we handle uninterpreted values in general.

  * Improve SMTLib logic-detection code to use generics.

### Version 8.8, 2020-09-04

  * Reworked uninterpreted sorts. Added new function `mkUninterpretedSort` to make
    declaration of completely uninterpreted sorts easier. In particular, we now
    automatically introduce the symbolic variant of the type (by prefixing the
    underlying type with `S`) so it becomes automatically available, both for uninterpreted
    sorts and enumerations. In the latter case, we also automatically introduce the value `sX`
    for each enumeration constant `X`, defined to be precisely `literal X`.

  * Handle incremental mode table-declarations that depend on freshly declared variables. Thanks
    to Gergő Érdi for reporting.

  * Fix a soundness bug in SFunArray caching. Thanks to Gergő Érdi for reporting. See
    https://github.com/LeventErkok/sbv/issues/541 for details.

  * Add support for the dReal solver, and introduce the notion of delta-satisfiability,
    where you can now check properties to be satisfiable against delta-perturbations.
    See "Documentation.SBV.Examples.DeltaSat.DeltaSat" for a basic example.

  * Add "extraArgs" parameter to SMTConfig to simplify passing extra command line
    arguments to the solver.

  * Add a method 

        sListArray :: (HasKind a, SymVal b) => b -> [(SBV a, SBV b)] -> array a b

    to the `SymArray` class, which allows for creation of arrays from lists of constant or 
    symbolic lists of pairs. The first argument is the value to use for uninitialized entries.
    Note that the initializer must be a known constant, i.e., it cannot be symbolic. Latter
    elements of the list will overwrite the earlier ones, if there are repeated keys.

  * Thanks to Jan Hrcek, a whole bunch of typos were fixed in the documentation and
    the source code. Much appreciated!

### Version 8.7, 2020-06-30

  * Add support for concurrent versions of solvers for query problems. Similar to
    `satWithAny`, `proveWithAny` etc., except when we have queries. Thanks to Jeffrey Young
    for the idea and the implementation.

  * Add "Documentation.SBV.Examples.Misc.Newtypes", demonstrating how to use newtypes
    over existing symbolic types as symbolic quantities themselves. Thanks to Curran McConnell
    for the example.

  * Added new predicate `sNotElem`, negating `sElem`.

  * Added new predicate `distinctExcept`. This is same as `distinct`
    except you can also provide an ignore list. The elements in
    the first list will be checked to be distinct from each other,
    or belong to the second list. This is good for writing constraints
    that either require a default value or if picked be different
    from each other for a set of variables. This sort of constraint
    can be coded in user space, but SBV generates efficient code
    instead of the obvious quadratic number of constraints.

  * Add function 'algRealToRational' that can convert an algebraic-real
    to a Haskell rational. We get an either value: If the algebraic real
    is exact, then it returns a 'Left' value that represents the value
    precisely. Otherwise, it returns a 'Right' value, which is only
    an approximation. Note: Setting 'printRealPrec' in SMTConfig
    to a higher value will increase the precision at the cost of more
    computation by the SMT solver.

  * Removed the 'SMTValue' class. It's functionality was not really
    needed. If you ever used this class, removing it from your
    type signatures should fix the issue. (You might have to
    add SymVal constraint if you did not already have it.) Please
    get in touch if you used this class in some cunning way and you
    need its functionality back.

  * Reworked SBVBenchSuite api, Phase 1 of BenchSuite completed.

  * Add support for addAxiom command to work in the interactive mode.
    Thanks to Martin Lundfall for the feedback.

  * Fixed `proveWithAny` and `satWithAny` functions so they properly
    kill the solvers that did not terminate first. Previously, they
    became zombies if they didn't end up quickly. Thanks to
    Robert Dockins for the investigation and the fix.

  * Fixed a bug where resetAssertions call was forgetting to restore the
    array and table contexts. Thanks to Martin Lundfall for reporting.

### Version 8.6, 2020-02-08

  * Fix typo in error message. Thanks to Oliver Charles
    for the patch.

  * Fix parsing of sequence counter-examples to accommodate
    recent changes in z3.

  * Add missing exports related to N-bit words. Thanks to
    Markus Barenhoff for the patch.

  * Generalized code-generation functions to accept a function
    with an arbitrary return type, which was previously just unit.
    This allows for complicated code-generation scenarios where
    one code-gen run can produce input to the next.

  * Scalability improvements for internal data structures. Thanks
    to Brian Huffman for the patch.

  * Add interpolation support for Z3, following changes to that
    solver. Note that SBV now supports two different APIs for
    interpolation extraction, one for Z3 and the other for
    MathSAT. This is unfortunate, but necessary since interpolant
    extraction isn't quite standardized amongst solvers and
    MathSAT and Z3 use sufficiently different calling mechanisms
    to warrant their own calls. See 'Documentation.SBV.Examples.Queries.Interpolants'
    for examples that illustrate both cases.

  * Add a new argument to `displayModels` function to allow rearranging
    of the results in an 'allSat` call. Strictly speaking this is
    a backwards breaking change, but substituting `id` for the
    new argument gives you old functionality, so easy to work-around.


### Version 8.5, 2019-10-16

  * Changes to compile with GHC 8.8. Thanks to Oliver Charles
    for the patch.

  * Minor fix to how kinds are shown for non-standard sizes.

  * Thanks to Jeffrey Young, SBV now has a performance benchmark
    test-suite. The framework still new, but should help
    in the long run to make sure SBV performance doesn't regress
    on its test-suite, and by extension in general usage.

### Version 8.4, 2019-08-31

  * SBV now supports arbitrary-size bit-vectors, i.e.,
    SWord 17, SInt 9, SWord 128 etc. These work like any
    other bit-vector, using the `DataKinds` feature of
    GHC. Thanks to Ben Blaxill for the idea and the initial
    implementation. Note that SBV still supports the traditional
    fixed-size bit-vectors, SInt8, SWord16 etc. Support for
    these will not be removed; so existing programs will
    continue to work.

  * To convert between arbitrary sized bit-vectors and
    the old style equivalents, use `fromSized` and `toSized`
    functions. The behavior is controlled with a closed
    type-family so you will get a (hopefully not too
    horrendous) type error message if you try to convert,
    say, a SInt16 to SInt 22; or vice versa.

  * Added arbitrary-sized bit vector operations: extraction,
    extension, and joining; these use proxy arguments to
    determine precise size info, and are much better suited
    for type safety. Consequently, removed the Splittable
    class which provided similar operations but only on
    predefined types. There is a new class called ByteConverter
    to convert to-and-from bytes for suitable bit-vector
    sizes up to 512.

  * Tuple construction functions are given new types to strengthen
    type checking. Previously the tuple argument was ignored,
    causing things to be marked as tuples when they actually
    cannot be. (NB. The system was always type-safe, it just
    didn't produce helpful type-error messages before.)

  * Model validator: In the presence of universally quantified
    variables, SBV used to refuse to validate given models. This
    is the right thing to do since we would have to validate
    the model for all possible values of all the universally
    quantified variables. Obviously this is not useful. Instead,
    SBV now simply assumes any universally quantified variable
    is zero during model validation. This severely limits the
    validation result, but it is better than nothing. (In the
    verbose mode, a message to this effect will be printed.)

  * Model validator: SBV can now validate models returned from
    the backend solver for regular-expression match problems.
    We also constant fold matches against constant strings without
    calling the solver at all, less useful perhaps but more inline
    with the general SBV methodology.

  * Add implementation of SHA-2 family of functions as an example
    algorithm.  These are good for code-generation purposes as
    opposed to actual verification tasks as it is hard to state
    any properties of these algorithms. But the SBV generated
    code can be quite useful in other development and verification
    environments. See 'Documentation.SBV.Examples.Crypto.SHA' for
    details.

  * Add 'cgShowU8UsingHex function, which controls if we print unsigned-8 bit
    values in code generation driver code in hex or not. Previously we were
    using decimal, but in crypto code hex is always better. Default is 'False'
    to keep backwards compatibility.

  * Add `sObserve` from: `SymWord a => String -> SBV a -> Symbolic ()` which
    comes in handy in symbolic contexts, especially with quick-check uses.

  * Ramped up travis-appveyor build infrastructure. However, we no
    longer test on the CI, since build-times are prohibitively long
    and myriad issues cause instability. If you can help out regarding
    testing on CI, please reach out!

### Version 8.3, 2019-06-08

  * Increment base dependency to 4.11.

  * Add support for `Data.Set.hasSize`.

  * Add `supportsFP` to CVC4 capabilities list. (#469)

  * Fix a glitch in allSat computations that incorrectly
    used values of internal variables in model construction.

  * SBV now directly uses the new `seq.nth` function from z3
    for sequence element access, instead of implementing it
    internally.

### Version 8.2, 2019-04-07

  * Fixed minor issue with getting observables in quantified contexts.

  * Simplify data-type constructor usage and accessor formats. See
    http://github.com/Z3Prover/z3/issues/2135 for a discussion.

  * Add support for model validation in optimization problems. Use the
    config parameter: `optimizeValidateConstraints`. Default: False. This
    feature nicely complements the `validateModel` option, which works
    for `sat` and `prove` calls. Note that when we validate the model
    for an optimization problem, we only make sure that the given result
    satisfies the constraints not that it is minimum (or maximum) such
    model. (And hence the new configuration variable.) Validating optimality
    is beyond the scope of SBV.

### Version 8.1, 2019-03-09

  * Added support for `SEither` and `SMaybe` types: symbolic sums and symbolic
    optional values. These can be accessed by importing `Data.SBV.Either` and
    `Data.SBV.Maybe` respectively. They translate to SMTLib's data-type syntax,
    and thus require a solver capable of handling datatypes. (Currently z3 and
    cvc4 are the only solvers that do.) All the typical introduction and
    elimination functions are provided, and these types integrate with all
    other symbolic types. (So you can have a list of SMaybe of SEither
    values, or at any nesting level.) Thanks to Joel Burget for the initial
    implementation of this idea and his contributions.

  * Added support for symbolic sets. The API closely follows that of `Data.Set`
    of Haskell, with some major differences: Symbolic sets can be co-finite.
    (That is, we can represent not only finite sets, but also sets whose complements
    are finite.) The distinction shows up in the `complement` operation, which
    is not supported in Haskell. All SBV sets can be complemented. On the flip
    side, SBV sets do not support a size operation (as they can be infinite),
    nor they can be converted to lists. See 'Data.SBV.Set' for the API documentation
    and "Documentation/SBV/Examples/Misc/SetAlgebra.hs" for an example that proves
    many familiar set properties.

  * SBV models now contain values for uninterpreted functions. This was a long
    requested feature, but there was no previous support since SMTLib does not
    have a standard way of querying such values. We now support this for z3 and
    cvc4: Note that SBV tries its best to interpret the output from these
    solvers, but it may give up if the response is too complicated (or something
    I haven't seen before!) due to non-standard format. Barring these details,
    the calls to `sat` now include function models, and you can also get them
    via `getFunction` in a query.

    For an example use case demonstrating how to use UF-models to synthesize a
    simple multiplier, see "Documentation/SBV/Examples/Uninterpreted/Multiply.hs".

  * SBV now comes with a model validator. In a 'sat', 'prove', or 'allSat' call,
    you can pass the configuration parameter 'z3{validateModel = True}' (or whichever
    solver you're using), and z3 will attempt to validate the returned model
    from the solver. Note that validation only works if there are no uninterpreted
    kinds of functions, and also in quantifier-free problems only. Please report
    your experiences, as there's room for improvement in validation, always!

  * [BACKWARDS COMPATIBILITY] The `allSat` function is similarly modified to
    return uninterpreted-function models. There are a few technical restrictions,
    however: Only the values of uninterpreted functions without any uninterpreted
    arguments will participate in `allSat` computation. (For instance,
    `uninterpret "f" :: SInteger -> SInteger` is OK, but
    `uninterpret "f" :: MyType -> SInteger` is not, where `MyType` itself
    is uninterpreted.) The reason for this is again there is no SMTLib way of
    reflecting uninterpreted model values back into the solver. This restriction
    should not cause much trouble in practice, but do get in touch if it is a
    use-case for you.

  * Added configuration option `allSatPrintAlong`. If set to True, calls to
    allSat will print their models as they are found. The default is False.

  * Added configuration parameter `satTrackUFs` (defaulting to True) to control
    if SBV should try to extract models for uninterpreted functions. In theory,
    this should always be True, but for most practical problems we typically
    don't care about the function values itself but that it exists. Set to 'False'
    if this is the case for your problem. Note that this setting is also respected
    in 'allSat' calls.

  * Added function `registerUISMTFunction`, which can be used to directly register uninterpreted
    functions. This is typically not necessary as uses of UI-functions do register them
    automatically, but it can come in handy in certain scenarios where there are no
    constraints on a UI-function other than its existence.

  * Added `Data.SBV.Tools.WeakestPreconditions` module, which provides a toy imperative
    language and an engine for checking partial and total correctness of imperative programs.
    It uses Dijkstra's weakest preconditions methodology to establish correctness claims.
    Loop invariants are required and must be supplied by the user. For total correctness,
    user must also provide termination measure functions. However, if desired, these can
    be skipped (by passing 'Nothing'), in which case partial correctness will be proven.
    Checking input parameters for no-change is supported via stability checks. For example
    use cases, see the `Documentation.SBV.Examples.WeakestPreconditions` directory.

  * Added functions `elem`/`notElem` to `Data.SBV.List`.

  * Added `snoc` (appending a single element at the end) to `Data.SBV.List` and `Data.SBV.String`.

  * Rework the 'Queriable' class to allow projection/embedding pairs. Also
    added a new 'Fresh' class, which is more usable in simpler scenarios
    where the default projection/embedding definitions are suitable.

  * Added strong-equality (.===) and inequality (./==) to the 'EqSymbolic' class. This
    method is equivalent to the usual (.==) and (./=) for all types except 'SFloat' and
    'SDouble'. For the floating types, it is object equality, that is 'NaN .=== Nan'
    and '0 ./== -0'. Use the regular equality for float/double's as they follow the
    IEEE754 rules, but occasionally we need to express object equality in a polymorphic
    way. Essentially this method is the polymorphic equivalent of 'fpIsEqualObject'
    except it works on all types.

  * Removed the redundant 'SDivisible' constraint on rotate-left and rotate-right operations.

  * Added unnamed equivalents of 'sBool', 'sWord8' etc; with a following underscore, i.e.,
    'sBool_', 'sWord8_'. The new functions are supported for all base types, chars,
    strings, lists, and tuples.

  * SBV now supports implicit constraints in the query mode, which were previously only
    available before user queries started.

  * Fixed a bug where hash-consing might reuse an expression even though the request might
    have been made at a different type. This is a rare case in SBV to happen due to types,
    but it was possible to exploit it in the Dynamic interface. Thanks to Brian Huffman
    for reporting and diagnosing the issue.

  * Fixed a bug where SBV was reporting incorrect "elapsed" time values, which are
    printed when the 'timing' configuration parameter is specified.

  * Documentation: Jan Path kindly fixed module headers of all the files to produce
    much better looking Haddock documents. Thanks Jan!

  * Added barrel-rotations (sBarrelRotateLeft-Right, svBarrelRotateLeft-Right) which
    can produce better code for verification by bit-blasting the rotation amount.
    It accepts bit-vectors as arguments and an unsigned rotation quantity to keep
    things simple.

  * Added new configuration option 'allowQuantifiedQueries', default is set to False.
    SBV normally doesn't allow quantifiers in a query context, because there are
    issues surrounding 'getValue'. However, Joel Burget pointed out this check
    is too strict for certain scenarios. So, as an escape hatch, you can define
    'allowQuantifiedQueries' to be 'True' and SBV will bypass this check. Of course,
    if you do this, then you are on your own regarding calls to `getValue` with
    quantified parameters! See http://github.com/LeventErkok/sbv/issues/459
    for details.

  * [BACKWARDS COMPATIBILITY] Renamed the class `IEEEFloatConvertable` to
    `IEEEFloatConvertible`. (Typo in name!) Matt Peddie pointed out issues
    regarding conversion of out-of-bounds float and double values to integral
    types. Unfortunately SMTLib does not support these conversions, and we
    had issues in getting Haskell, SMTLib, and C to agree. Summary: These conversions
    are only guaranteed to work if they are done on numbers that lie within the
    representable range of the target type. Thanks to Matt Peddie for pointing out
    the out-of-bounds problem, his help in figuring out the issues.

  * [BACKWARDS COMPATIBILITY] The 'AllSat' result now tracks if search has stopped
    because the solver returned 'Unknown'. Previously this information was not
    displayed.

  * [BACKWARDS COMPATIBILITY, Internal] Several constraints on internal
    classes (such as SymVal, EqSymbolic, OrdSymbolic) were reworked to
    reflect the dependencies better. Strictly speaking this is a backwards
    compatibility breaking change, but I doubt it'll impact any user
    code; though you might have to add some extra constraints if you were
    writing sufficiently polymorphic SBV code. Yell if you find otherwise!

  * [BACKWARDS COMPATIBILITY] SBV now allows user-given names to be duplicated.
    It will implicitly add a suffix to them to distinguish without complaining. (In
    previous versions, we would error out.) The reason for this change is that
    sometimes it's nice to be able to simply give a prefix for a class of names
    and not worry about the actual name itself. (Note that this will cause issues
    if you use model-extraction-via-maps method if we ever make a name unique
    and store it under a different name, but that's hardly ever used feature and
    arguably the right thing to do anyway.) Thanks to Joel Burget for suggesting
    the idea.

  * [BACKWARDS COMPATIBILITY, Internal] SBV is now more strict in how user-queries
    are used, performing certain extra-checks that were not done before. (For instance,
    previously it was possible to mix prove-sat with a query call, which should
    not have been allowed.) If you have any code that breaks for this reason, you
    probably should've written it in some other way to start with. Please get
    in touch if that is the case.

  * [BACKWARDS COMPATIBILITY] You need at least GHC 8.4.1 to compile SBV.
    If you're stuck with an older version, let me know and we'll see if
    we can create a custom version for you; though I'd much rather avoid this
    if at all possible.

  * SBV now supports optimization of goals of SDouble and SFloat types. This is
    done using the lexicographic ordering on floats, and adds on the additional
    constraint that the resulting float is not a NaN. If you use this feature,
    then your float value will be minimized as the corresponding 32 (or 64 for
    doubles) bit word. Note that this methods supports infinities properly, and
    does not distinguish between -0 and +0.

  * Optimization routines have been generalized to work over arbitrary metric-spaces,
    with user-definable mappings. The simplest instance we have added is optimization
    over booleans, by the obvious numeric mapping. Tuples are also supported with
    the usual lexicographic ordering. In addition, SBV can now optimize over
    user-defined enumerations. See "Documentation.SBV.Examples.Optimization.Enumerate" for
    an example.

  * Improved the internal representation of constraints to address performance
    issues See http://github.com/LeventErkok/sbv/issues/460 for details. Thanks to
    Thanks Jeffrey Young for reporting.

### Version 8.0, 2019-01-14

  * This is a major release of SBV, with several BACKWARDS COMPATIBILITY breaking
    changes. Lots of reworking of the internals to modernize the SBV code base.
    A few external API changes happened as well, mainly in terms of renamed
    types/operators to reflect the current state of things. I expect most end user
    programs to carry over unchanged, perhaps needing a bunch of renames. See below
    for details.

  * Transformer stack and `SymbolicT`: This major internal revamping was contributed
    by Brian Schroeder. Brian reworked the internals of SBV to allow for custom monad
    stacks. In particular, there is now a `SymbolicT` monad transformer, which
    generalizes the `Symbolic` monad over an arbitrary base type, allowing users to
    build SBV based symbolic execution engines on top of their own monad infrastructure.

    Brian took the pains to ensure existing users (or those who do not have their
    own monad stack), the transformer capabilities remain transparent. That is,
    your existing code should recompile as is, or perhaps with minor aesthetic
    changes. Please report if you find otherwise, or need help.

    See `Documentation.SBV.Examples.Transformers.SymbolicEval` for an example of
    how to use the transformer based code.

    Thanks to Brian Schroeder for this massive effort to modernize the SBV code-base!

  * Support for tuples: Thanks to Joel Burget, SBV now supports tuple types (up-to
    8-tuples), and allows mixing and matching of lists and tuples arbitrarily
    as symbolic values. For instance `SBV [(Integer, String)]` is a valid type as
    is `SBV [(Integer, [(Char, (Float, String))])]`, with each component symbolically
    represented. Along with `STuple` for regular 2-tuples, there are new types
    for `STupleN` for `N` between 2 to 8, along with `untuple` destructor, and field
    accessors similar to lens: For instance `p^._4` would project the 4th element of
    a tuple that has at least 4 fields. The mixing and matching of field types and
    nesting allows for very rich symbolic value representations. See
    `Documentation.SBV.Examples.Misc.Tuple` for an example.

  * [BACKWARDS COMPATIBILITY] The `Boolean` class is removed, which used to abstract
    over logical connectives. Previously, this class handled 'SBool' and 'Bool', but
    the generality was hardly ever used and caused typing ambiguities. The new
    implementation simplifies boolean operators to simply operate on the `SBool`
    type. Also changed the operator names to fit with all the others by starting
    them with dots. A simple conversion guide:

        * Literal True : true    became   sTrue
        * Literal False: false   became   sFalse
        * Negation     : bNot    became   sNot
        * Conjunction  : &&&     became   .&&
        * Disjunction  : |||     became   .||
        * XOr          : <+>     became   .<+>
        * Nand         : ~&      became   .~&
        * Nor          : ~|      became   .~|
        * Implication  : ==>     became   .=>
        * Iff          : <=>     became   .<=>
        * Aggregate and: bAnd    became   sAnd
        * Aggregate or : bOr     became   sOr
        * Existential  : bAny    became   sAny
        * Universal    : bAll    became   sAll

  * [BACKWARDS COMPATIBILITY, INTERNAL] Historically, SBV focused on bit-vectors and machine
    words, which meant lots of internal types were named suggestive of this heritage.
    With the addition of `SInteger`, `SReal`, `SFloat`, `SDouble` we have expanded
    this, but still remained focused on atomic types. But, thanks largely to
    Joel Burget, SBV now supports symbolic characters, strings, lists, and now
    tuples, and nested tuples/lists, which makes this word-oriented naming confusing.
    To reflect, we made the following internal renamings:

        * SymWord     became      SymVal
        * SW          became      SV
        * CW          became      CV
        * CWVal       became      CVal

    Along with these, many of the internal constructor/variable names also changed in
    a similar fashion.

    For most casual users, these changes should not require any changes. But if you were
    developing libraries on top of SBV, then you will have to adapt to the new schema.
    Please report if there are any gotchas we have forgotten about.

  * [BACKWARDS COMPATIBILITY] When user queries are present, SBV now picks the logic
    "ALL" (as opposed to a suitable variant of bit-vectors as in the past versions).
    This can be overridden by the 'setLogic' command as usual of course. While the new
    choice breaks backwards compatibility, I expect the impact will be minimal, and
    the new behavior matches better with user expectations on how external queries are
    usually employed.

  * [BACKWARDS COMPATIBILITY] Renamed the module `Data.SBV.List.Bounded` to
    `Data.SBV.Tools.BoundedList`.

  * Introduced a `Queriable` class, which simplifies symbolic programming with composite
    user types. See `Documentation.SBV.Examples.ProofTools` directory for several
    use cases and examples.

  * Added function `observeIf`, companion to `observe`. Allows observing of values
    if they satisfy a given predicate.

  * Added function `ensureSat`, which makes sure the solver context is satisfiable
    when called in the query mode. If not, an error will be thrown. Simplifies
    programming when we expect a satisfiable result and want to bail out if otherwise.

  * Added `nil` to `Data.SBV.List`. Added `nil` and `uncons` to `Data.SBV.String`.
    These were inadvertently left out previously.

  * Add `Data.SBV.Tools.BMC` module, which provides a BMC (bounded-model
    checking engine) for traditional state transition systems. See
    `Documentation.SBV.Examples.ProofTools.BMC` for example uses.

  * Add `Data.SBV.Tools.Induction` module, which provides an induction engine
    for traditional state transition systems. Also added several example use
    cases in the directory `Documentation.SBV.Examples.ProofTools`.

### Version 7.13, 2018-12-16

  * Generalize the types of `bminimum` and `bmaximum` by removing the `Num`
    constraint.

  * Change the type of `observe` from: `SymWord a => String -> SBV a -> Symbolic ()`
    to `SymWord a => String -> SBV a -> SBV a`. This allows for more concise observables,
    like this:

        prove $ \x -> observe "lhs" (x+x) .== observe "rhs" (2*x+1)
        Falsifiable. Counter-example:
          s0  = 0 :: Integer
          lhs = 0 :: Integer
          rhs = 1 :: Integer

  * Add `Data.SBV.Tools.Range` module which defines `ranges` and `rangesWith` functions: They
    compute the satisfying contiguous ranges for predicates with a single variable. See
    `Data.SBV.Tools.Range` for examples.

  * Add `Data.SBV.Tools.BoundedFix` module, which defines the operator `bfix` that can be used
    as a bounded fixed-point operator for use in bounded-model-checking like algorithms. See
    `Data.SBV.Tools.BoundedFix` for some example use cases.

  * Fix list-element extraction code, which asserted too strong a constraint. See issue #421
    for details. Thanks to Joel Burget for reporting.

  * New bounded list functions: `breverse`, `bsort`, `bfoldrM`, `bfoldlM`, and `bmapM`.
    Contributed by Joel Burget.

  * Add two new puzzle examples:
       * `Documentation.SBV.Examples.Puzzles.LadyAndTigers`
       * `Documentation.SBV.Examples.Puzzles.Garden`

### Version 7.12, 2018-09-23

  * Modifications to make SBV compile with GHC 8.6.1. (SBV should
    now compile fine with all versions of GHC since 8.0.1; and
    possibly earlier. Please report if you are using a version
    in this range and have issues.)

  * Improve the BoundedMutex example to show a non-fair trace.
    See `Documentation/SBV/Examples/Lists/BoundedMutex.hs`.

  * Improve Haddock documentation links throughout.

### Version 7.11, 2018-09-20

  * Add support for symbolic lists. (That is, arbitrary but fixed length symbolic
    lists of integers, floats, reals, etc. Nested lists are allowed as well.)
    This is building on top of Joel Burget's initial work for supporting symbolic
    strings and sequences, as supported by Z3. Note that the list theory solvers
    are incomplete, so some queries might receive an unknown answer. See
    `Documentation/SBV/Examples/Lists/Fibonacci.hs` for an example, and the
    module `Data.SBV.List` for details.

  * A new module `Data.SBV.List.Bounded` provides extra functions to manipulate
    lists with given concrete bounds. Note that SMT solvers cannot deal with
    recursive functions/inductive proofs in general, so the utilities in this
    file can come in handy when expressing bounded-model-checking style
    algorithms. See `Documentation/SBV/Examples/Lists/BoundedMutex.hs` for a
    simple mutex algorithm proof.

  * Remove dependency on data-binary-ieee754 package; which is no longer
    supported.

### Version 7.10, 2018-07-20
  * [BACKWARDS COMPATIBILITY] '==' and '/=' now always throw an error instead of
    only throwing an error for non-concrete values.
    http://github.com/LeventErkok/sbv/issues/301

  * [BACKWARDS COMPATIBILITY] Array declarations are reworked to take
    an initial value. The call 'newArray' now accepts an optional default
    value, which itself can be symbolic. If provided, the array will return
    the given value for all reads from uninitialized locations. If not given,
    then reads from unwritten locations produce uninterpreted constants. The
    behavior of 'SFunArray' and 'SArray' is exactly the same in this regard.
    Note that this is a backwards-compatibility breaking change, as you need
    to pass a 'Nothing' argument to 'newArray' to get the old behavior.
    (Solver note: If you use 'SFunArray', then defaults are fully supported
    by SBV since these are internally handled, concrete or symbolic. If you
    use 'SArray', which gets translated to SMTLib, then MathSAT and Z3 supports
    default values with both concrete and symbolic cases, CVC4 only supports
    if they are constants. Boolector and Yices don't support default values
    at this point in time, and ABC doesn't support arrays at all.)

  * [BACKWARDS COMPATIBILITY] SMTException type has been renamed to
    SBVException. SBV now throws this exception in more cases to aid in
    building tools on top of SBV that might want to deal with exceptions
    in different ways. (Previously, we used to call 'error' instead.)

  * [BACKWARDS COMPATIBILITY] Rename 'assertSoft' to 'assertWithPenalty', which
    better reflects the nature of this function. Also add extra checks to warn
    the user if optimization constraints are present in a regular sat/prove call.

  * Implement `softConstrain`: Similar to 'constrain', except the solver is
    free to leave it unsatisfied (i.e., leave it false) if necessary to
    find a satisfying solution. Useful in modeling conditions that are
    "nice-to-have" but not "required." Note that this is similar to
    'assertWithPenalty', except it works in non-optimization contexts.
    See `Documentation.SBV.Examples.Misc.SoftConstrain` for a simple example.

  * Add 'CheckedArithmetic' class, which provides bit-vector arithmetic
    operations that do automatic underflow/overflow checking. The operations
    follow their regular counter-parts, with an exclamation mark added at
    the end: +!, -!, *!, /!. There is also negateChecked, for the same
    function on unary negation. If you program using these functions,
    then you can call 'safe' on the resulting programs to make sure
    these operations never cause underflow and overflow conditions.

  * Similar to above, add 'sFromIntegralChecked', providing overflow/underflow
    checks for cast operations.

  * Add `Documentation.SBV.Examples.BitPrecise.BrokenSearch` module to show the
    use of overflow checking utilities, using the classic broken binary search
    example from http://ai.googleblog.com/2006/06/extra-extra-read-all-about-it-nearly.html

  * Fix an issue where SBV was not sending array declarations to the SMT-solver
    if there were no explicit constraints. Thanks to Oliver Charles for reporting.

  * Rework 'SFunArray' implementation, addressing performance issues. We now
    carefully memoize elements as we do the look-ups. This addresses several
    performance issues that came up; hopefully providing some relief. The
    function 'mkSFunArray' is also removed, which used to lift Haskell
    functions to such arrays, often used to implement initial values. Now,
    if a read is done on an unwritten element of 'SFunArray' we get an
    uninterpreted constant. This is inline with how 'SArray' works, and
    is consistent. The old 'SFunArray' implementation based on functions
    is no longer available, though it is easy to implement it in user-space
    if needed. Please get in contact if this proves to be an issue.

  * Add 'freshArray' to allow for creation of existential fresh arrays in the query mode.
    This is similar to 'newArray' which works in the Symbolic mode, and is analogous to
    'freshVar'. Most users shouldn't need this as 'newArray' calls should suffice. Only
    use if you need a brand new array after switching to query mode.

  * SBV now rejects queries if universally quantified inputs are present. Previously
    these were allowed to go through, but in general skolemization makes the corresponding
    variables unusable in the query context. See http://github.com/LeventErkok/sbv/issues/407
    for details. If you have an actual use case for such a feature, please get in
    touch. Thanks to Brian Schroeder for reporting this anomaly.

  * Export 'addSValOptGoal' from 'Data.SBV.Internals', to help with 'Metric' class
    instantiations. Requested by Dan Rosen.

  * Export 'registerKind' from 'Data.SBV.Internals', to help with custom array declarations.
    Thanks to Brian Schroeder for the patch.

  * If an asynchronous exception is caught, SBV now throws it back without further processing.
    (For instance, if the backend solver gets killed. Previously we were turning these into
    synchronous errors.) Thanks to Oliver Charles for pointing out this corner case.

### Version 7.9, 2018-06-15

  * Add support for bit-vector arithmetic underflow/overflow detection. The new
    'ArithmeticOverflow' class captures conditions under which addition, subtraction,
    multiplication, division, and negation can underflow/overflow for
    both signed and unsigned bit-vector values. The implementation is based on
    http://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/z3prefix.pdf,
    and can be used to detect overflow caused bugs in machine arithmetic.
    See `Data.SBV.Tools.Overflow` for details.

  * Add 'sFromIntegralO', which is the overflow/underflow detecting variant
    of 'sFromIntegral'. This function returns (along with the converted
    result), a pair of booleans showing whether the conversion underflowed
    or overflowed.

  * Change the function 'getUnknownReason' to return a proper data-type
    ('SMTReasonUnknown') as opposed to a mere string. This is at the
    query level. Similarly, change `Unknown` result to return the same
    data-type at the sat/prove level.

  * Interpolants: With Z3 4.8.0 release, Z3 folks have dropped support
    for producing interpolants. If you need interpolants, you will have
    to use the MathSAT backend now. Also, the MathSAT API is slightly
    different from how Z3 supported interpolants as well, which means
    your old code will need some modifications. See the example in
    Documentation.SBV.Examples.Queries.Interpolants for the new usage.

  * Add 'constrainWithAttribute' call, which can be used to attach
    arbitrary attribute to a constraint. Main use case is in interpolant
    generation with MathSAT.

  * C code generation: SBV now spits out linker flag -lm if needed.
    Thanks to Matt Peddie for reporting.

  * Code reorg: Simplify constant mapping table, by properly accounting
    for negative-zero floats.

  * Export 'sexprToVal' for the class SMTValue, which allows for custom
    definitions of value extractions. Thanks to Brian Schroeder for the
    patch.

  * Export 'Logic' directly from Data.SBV. (Previously was from Control.)

  * Fix a long standing issue (ever since we introduced queries) where
    'sAssert' calls were run in the context of the final output boolean,
    which is simply the wrong thing to do.

### Version 7.8, 2018-05-18

  * Fix printing of min-bounds for signed 32/64 bit numbers in C
    code generation: These are tricky since C does not allow
    -min_value as a valid literal!  Instead we use the macros provided in
    stdint.h. Thanks to Matt Peddie for reporting this corner case.

  * Fix translation of the `abs` function in C code generation, making
    sure we use the correct variant. Thanks to Matt Peddie for reporting.

  * Fix handling of tables and arrays in pushed-contexts. Previously,
    we used initializers to get table/array values stored properly.
    However, this trick does not work if we are in a pushed-context;
    since a pop can forget the corresponding assignments. SBV now
    handles this corner case properly, by using tracker assertions
    to keep track of what array values must be restored at each pop.
    Thanks to Martin Brain on the SMTLib mailing list for the
    suggestion. (See http://github.com/LeventErkok/sbv/issues/374
    for details.)

  * Fix corner case in ite branch equality with float/double arguments,
    where we were previously confusing +/-0 as equal to each other.
    Thanks to Matt Peddie for reporting.

  * Add a call 'cgOverwriteFiles', which suppresses code-generation
    prompts for overwriting files and quiets the prompts during
    code generation. Thanks to Matt Peddie for the suggestion.

  * Add support for uninterpreted function introductions in the query
    mode. Previously, this was only allowed before the query started,
    now we fully support uninterpreted functions in all modes.

  * New example: Documentation/SBV/Examples/Puzzles/HexPuzzle.hs,
    showing how to code cover properties using SBV, using a form
    of bounded model checking.

### Version 7.7, 2018-04-29

  * Add support for Symbolic characters ('SChar') and strings ('SString'.)
    Thanks to Joel Burget for the initial implementation.

    The 'SChar' type currently corresponds to the Latin-1 character
    set, and is thus a subset of the Haskell 'Char' type. This is
    due to the current limitations in SMT-solvers. However, there
    is a pending SMTLib proposal to support unicode, and SBV will track
    these changes to have full unicode support: For further details
    see: http://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml

    The 'SString' type is the type of symbolic strings, consisting
    of characters from the Latin-1 character set currently, just
    like the planned 'SChar' improvements. Note that an 'SString'
    is *not* simply a list of 'SChar' values: It is a symbolic
    type of its own and is processed as a single item. Conversions
    from list of characters is possible (via the 'implode' function).
    In the other direction, one cannot generally 'explode' a string,
    since it may be of arbitrary length and thus we would not know
    what concrete list to map it to. This is a bit unlike Haskell,
    but the differences dissipate quickly in general, and the power
    of being able to deal with a string as a symbolic entity on its
    own opens up many verification possibilities.

    Note that currently only Z3 and CVC4 has support for this logic,
    and they do differ in some details. Various character/string
    operations are supported, including length, concatenation,
    regular-expression matching, substrig operations, recognizers, etc.
    If you use this logic, you are likely to find bugs in solvers themselves
    as support is rather new: Please report.

  * If unsat-core extraction is enabled, SBV now returns the unsat-core
    directly with in a solver result. Thanks to Ara Adkins for the
    suggestion.

  * Add 'observe'. This function allows internal expressions to be
    given values, which will be part of the satisfying model or
    the counter-example upon model construction. Useful for tracking
    expected/returned values. Also works with quickCheck.

  * Revamp Haddock documentation, hopefully easier to follow now.

  * Slightly modify the generated-C headers by removing whitespace.
    This allows for certain "lint" rules to pass when SBV generated
    code is used in conjunction with a larger code base. Thanks
    to Greg Horn for the pull request.

  * Improve implementation of 'svExp' to match that of '.^', making
    it more defined when the exponent is constant. Thanks to Brian
    Huffman for the patch.

  * Export the underlying polynomial representation for algorithmic
    reals from the Internals module for further user processing.
    Thanks  to Jan Path for the patch.

### Version 7.6, 2018-03-18

  * GHC 8.4.1 compatibility: Work around compilation issues. SBV
    now compiles cleanly with GHC 8.4.1.

  * Define and export sWordN, sWordN_, sIntN_, from the Dynamic
    interface, which simplifies creation of variables of arbitrary
    bit sizes. These are similar to sWord8, sInt8, etc.; except
    they create dynamic counterparts that can be of arbitrary bit size.

### Version 7.5, 2018-01-13

  * Remove obsolete references to tactics in a few haddock comments. Thanks
    to Matthew Pickering for reporting.

  * Added logic Logic_NONE, to be used in cases where SBV should not
    try to set the logic. This is useful when there is no viable value to
    set, and the back-end solver doesn't understand the SMT-Lib convention
    of using "ALL" as the logic name. (One example of this is the Yices
    solver.)

  * SBV now returns SMTException (instead of just calling error) in case
    the backend solver responds with error message. The type SMTException
    can be caught by the user programs, and it includes many fields as an
    indication of what went wrong. (The command sent, what was expected,
    what was seen, etc.) Note that if this exception is ever caught, the
    backend solver is no longer alive: You should either just throw it,
    or perform proper clean-up on your user code as required to set up
    a new context. The provided show instance formats the exception nicely
    for display purposes. See http://github.com/LeventErkok/sbv/issues/335
    for details and thanks to Brian Huffman for reporting.

  * SIntegral class now has Integral as a super-class, which ensures the
    base-type it's used at is Integral. This was already true for all instances,
    so we are just making it more explicit.

  * Improve the implementation of .^ (exponentiation) to cover more cases,
    in particular signed exponents are now OK so long as they are concrete
    and positive, following Haskell convention.

  * Removed the 'FromBits' class. Its functionality is now merged with the
    new 'SFiniteBits' class, see below.

  * Introduce 'SFiniteBits' class, which only incorporates finite-words in it,
    i.e., SWord/SInt for 8-16-32-64. In particular it leaves out SInteger,
    SFloat, SDouble, and SReal. Important in recognizing bit-vectors of
    finite size, essentially. Here are the methods:

        class (SymWord a, Num a, Bits a) => SFiniteBits a where
            sFiniteBitSize      :: SBV a -> Int                     -- ^ Bit size
            lsb                 :: SBV a -> SBool                   -- ^ Least significant bit of a word, always stored at index 0.
            msb                 :: SBV a -> SBool                   -- ^ Most significant bit of a word, always stored at the last position.
            blastBE             :: SBV a -> [SBool]                 -- ^ Big-endian blasting of a word into its bits. Also see the 'FromBits' class.
            blastLE             :: SBV a -> [SBool]                 -- ^ Little-endian blasting of a word into its bits. Also see the 'FromBits' class.
            fromBitsBE          :: [SBool] -> SBV a                 -- ^ Reconstruct from given bits, given in little-endian
            fromBitsLE          :: [SBool] -> SBV a                 -- ^ Reconstruct from given bits, given in little-endian
            sTestBit            :: SBV a -> Int -> SBool            -- ^ Replacement for 'testBit', returning 'SBool' instead of 'Bool'
            sExtractBits        :: SBV a -> [Int] -> [SBool]        -- ^ Variant of 'sTestBit', where we want to extract multiple bit positions.
            sPopCount           :: SBV a -> SWord8                  -- ^ Variant of 'popCount', returning a symbolic value.
            setBitTo            :: SBV a -> Int -> SBool -> SBV a   -- ^ A combo of 'setBit' and 'clearBit', when the bit to be set is symbolic.
            fullAdder           :: SBV a -> SBV a -> (SBool, SBV a) -- ^ Full adder, returns carry-out from the addition. Only for unsigned quantities.
            fullMultiplier      :: SBV a -> SBV a -> (SBV a, SBV a) -- ^ Full multiplier, returns both high and low-order bits. Only for unsigned quantities.
            sCountLeadingZeros  :: SBV a -> SWord8                  -- ^ Count leading zeros in a word, big-endian interpretation
            sCountTrailingZeros :: SBV a -> SWord8                  -- ^ Count trailing zeros in a word, big-endian interpretation

    Note that the functions 'sFiniteBitSize', 'sCountLeadingZeros', and 'sCountTrailingZeros' are
    new. Others have existed in SBV before, we are just grouping them together now in this new class.

  * Tightened certain signatures where SBV was too liberal, using the SFiniteBits class. New signatures are:

         sSignedShiftArithRight :: (SFiniteBits a, SIntegral b) => SBV a -> SBV b -> SBV a
         crc                    :: (SFiniteBits a, SFiniteBits b) => Int -> SBV a -> SBV b -> SBV b
         readSTree              :: (SFiniteBits i, SymWord e) => STree i e -> SBV i -> SBV e
         writeSTree             :: (SFiniteBits i, SymWord e) => STree i e -> SBV i -> SBV e -> STree i e

    Thanks to Thomas DuBuisson for reporting.

### Version 7.4, 2017-11-03

  * Export queryDebug from the Control module, allowing custom queries to print
    debugging messages with the verbose flag is set.

  * Relax value-parsing to allow for non-standard output from solvers. For
    instance, MathSAT/Yices prints reals as integers when they do not have a
    fraction. We now support such cases, relaxing the standard slightly. Thanks
    to Geoffrey Ramseyer for reporting.

  * Fix optimization routines when applied to signed-bitvector goals. Thanks
    to Anders Kaseorg for reporting. Since SMT-Lib does not distinguish between
    signed and unsigned bit-vectors, we have to be careful when expressing goals
    that are over signed values. See http://github.com/LeventErkok/sbv/issues/333
    for details.

### Version 7.3, 2017-09-06

  * Query mode: Add support for arrays in query mode. Thanks to Brad Hardy for
    providing the use-case and debugging help.

  * Query mode: Add support for tables. (As used by 'select' calls.)

### Version 7.2, 2017-08-29

  * Reworked implementation of shifts and rotates: When a signed quantity was
    being shifted right by more than its size, SBV used to return 0. Robert Dockins pointed
    out that the correct answer is actually -1 in such cases. The new implementation
    merges the dynamic and typed interfaces, and drops support for non-constant shifts
    of unbounded integers, which is not supported by SMTLib. Thanks to Robert for
    reporting the issue and identifying the root cause.

  * Rework how quantifiers are handled: We now generate separate asserts for
    prefix-existentials. This allows for better (smaller) quantified code, while
    preserving semantics.

  * Rework the interaction between quantifiers and optimization routines.
    Optimization routines now properly handle quantified formulas, so long as the
    quantified metric does not involve any universal quantification itself. Thanks
    to Matthew Danish for reporting the issue.

  * Development/Infrastructure: Lots of work around the continuous integration
    for SBV. We now build/test on Linux/Mac/Windows on every commit. Thanks to
    Travis/Appveyor for providing free remote infrastructure. There are still
    gotchas and some reductions in tests due to host capacity issues. If you
    would like to be involved and improve the test suite, please get in touch!

### Version 7.1, 2017-07-29

  * Add support for 'getInterpolant' in Query mode.

  * Support for SMT-results that can contain multi-line strings, which
    is rare but it does happen. Previously SBV incorrectly interpreted such
    responses to be erroneous.

  * Many improvements to build infrastructure and code clean-up.

  * Fix a bug in the implementation of `svSetBit`. Thanks to Robert Dockins
    for the report.

### Version 7.0, 2017-07-19

  * NB. SBV now requires GHC >= 8.0.1 to compile. If you are stuck with an older
    version of GHC, please get in contact.

  * This is a major rewrite of the internals of SBV, and is a backwards compatibility
    breaking release. While we kept the top-level and most commonly used APIs the
    same (both types and semantics), much of the internals and advanced features
    have been rewritten to move SBV to a new model of execution: SBV no longer
    runs your program symbolically and calls the SMT solver afterwards. Instead,
    the interaction with the solver happens interleaved with the actual program execution.
    The motivation is to allow the end-users to send/receive arbitrary SMTLib
    commands to the solver, instead of the cooked-up recipes. SBV still provides
    all the recipes for its existing functionality, but users can now interact
    with the solver directly. See the module `Data.SBV.Control` for the main
    API, together with the new functions 'runSMT' and 'runSMTWith'.

  * The 'Tactic' based solver control (introduced in v6.0) is completely removed, and
    is replaced by the above described mechanism which gives the user a lot of
    flexibility instead. Use queries for anything that required a tactic before.

  * The call 'allSat' has been reworked so it performs only one call to the underlying
    solver and repeatedly issues check-sat to get new assignments. This differs from the
    previous implementation where we spun off a new call to the executable for each
    successive model. While this is more efficient and much more preferable, it also
    means that the results are no longer lazily computed: If there is an infinite number
    of solutions (or a very large number), you can no longer merely do a 'take' on the result.
    While this is inconvenient, it fits better with our new methodology of query based
    interaction. Note that the old behavior can be modeled, if required, by the user; by explicitly
    interleaving the calls to 'sat.' Furthermore, we now provide a new configuration
    parameter named 'allSatMaxModelCount' which can be used to limit the number models we
    seek. The default is to get all models, however long that might take.

  * The Bridge modules (`Data.SBV.Bridge.Yices`, `Data.SBV.Bridge.Z3`) etc. are
    all removed. The bridge functionality was hardly used, where different solvers
    were much easier to access using the `with` functions. (Such as `proveWith`,
    `satWith` etc.) This should result in no loss of functionality, except for
    occasional explicit mention of solvers in your code, if you were using
    bridge modules to start with.

  * Optimization routines have been changed to take a priority as an argument, (i.e.,
    Lexicographic, Independent, etc.). The old method of supplying the priority
    via tactics is no longer supported.

  * Pareto-front extraction has been reworked, reflecting the changes in Z3 for
    this functionality. Since pareto-fronts can be infinite in number, the user
    is now allowed to specify a "limit" to stop the solver from querying ad
    infinitum. If the limit is not specified, then sbv will query till it
    exhausts all the pareto-fronts, or till it runs out of memory in case there
    is an infinite number of them.

  * Extraction of unsat-cores has changed. To use this feature, we now use
    custom queries. See `Data.SBV.Examples.Misc.UnsatCore` for an example.
    Old style of unsat-core extraction is no longer supported.

  * The 'timing' option of SMTConfig has been reworked. Since we now start the
    solver immediately, it is no longer sensible to distinguish between "SBV" time,
    "translation" time etc. Instead, we print one simple "Elapsed" time if requested.
    If you need a detailed timing analysis, use the new 'transcript' option to
    SMTConfig: It will produce a file with precise timing intervals for each
    command issued to help you figure out how long each step took.

  * The following functions have been reworked, so they now also return
    the time-elapsed for each solver:

        satWithAll   :: Provable a => [SMTConfig] -> a -> IO [(Solver, NominalDiffTime, SatResult)]
        satWithAny   :: Provable a => [SMTConfig] -> a -> IO  (Solver, NominalDiffTime, SatResult)
        proveWithAll :: Provable a => [SMTConfig] -> a -> IO [(Solver, NominalDiffTime, ThmResult)]
        proveWithAny :: Provable a => [SMTConfig] -> a -> IO  (Solver, NominalDiffTime, ThmResult)

  * Changed the way `satWithAny` and `proveWithAny` works. Previously, these
    two functions ran multiple solvers, and took the result of the first
    one to finish, killing all the others. In addition, they *waited* for
    the still-running solvers to finish cleaning-up, as sending a 'ThreadKilled'
    is usually not instantaneous. Furthermore, a solver might simply take
    its time! We now send the interrupt but do not wait for the process to
    actually terminate. In rare occasions this could create zombie processes
    if you use a solver that is not cooperating, but we have seen not insignificant
    speed-ups for regular usage due to ThreadKilled wait times being rather long.

  * Configuration option `useLogic` is removed. If required, this should
    be done by a call to the new 'setLogic' function:

        setLogic QF_NRA

  * Configuration option `timeOut` is removed. This was rarely used, and the solver
    support was rather sketchy. We now have a better mechanism in the query mode
    for timeouts, where it really matters. Please get in touch if you relied on
    this old mechanism. Correspondingly, the functions `isTheorem`, `isSatisfiable`,
    `isTheoremWith` and `isSatisfiableWith` had their time-out arguments removed
    and return types simplified.

  * The function 'isSatisfiableInCurrentPath' is removed. Proper queries should be used
    for what this function tentatively attempted to provide. Please get in touch
    if you relied on this function and want to restructure your code to use proper queries.

  * Configuration option 'smtFile' is removed. Instead use 'transcript' now, which
    provides a much more detailed output that is directly loadable to a solver
    and has an accurate account of precisely what SBV sent.

  * Enumerations are now much easier to use symbolically, with the addition
    of the template-haskell splice mkSymbolicEnumeration. See `Data/SBV/Examples/Misc/Enumerate.hs`
    for an example.

  * Thanks to Kanishka Azimi, our external test suite is now run by
    Tasty! Kanishka modernized the test suite, and reworked the
    infrastructure that was showing its age. Thanks!

  * The function pConstrain and the Data.SBV.Tools.ExpectedValue are
    removed. Probabilistic constraints were rarely used, and if
    necessary can be implemented outside of SBV. If you were using
    this feature, please get in contact.

  * SArray and SFunArray has been reworked, and they no longer take
    and initial value. Similarly resetArray has been removed, as it
    did not really do what it advertised. If an initial value is needed,
    it is best to code this explicitly in your model.

### Version 6.1, 2017-05-26

  * Add support for unsat-core extraction. To use this feature, use
    the `namedConstraint` function:

        namedConstraint :: String -> SBool -> Symbolic ()

    to associate a label to a constrain or a boolean term that
    can later be labeled by the backend solver as belonging to the
    unsat-core.

    Unsat-cores are not enabled by default since they can be
    expensive; to use:

        satWith z3{getUnsatCore=True} $ do ...

    In the programmatic API, the function:

        extractUnsatCore :: Modelable a => a -> Maybe [String]

    can be used to programmatically extract the unsat-core. Note that
    backend solvers will only include the named expressions in the unsat-core,
    i.e., any unnamed yet part-of-the-core-unsat expressions will be missing;
    as speculated in the SMT-Lib document itself.

    Currently, Z3, MathSAT, and CVC4 backends support unsat-cores.

    (Thanks to Rohit Ramesh for the suggestion leading to this feature.)

  * Added function `distinct`, which returns true if all the elements of the
    given list are different. This function replaces the old `allDifferent`
    function, which is now removed. The difference is that `distinct` will produce
    much better code for SMT-Lib. If you used `allDifferent` before, simply
    replacing it with `distinct` should work.

  * Add support for pseudo-boolean operations:

          pbAtMost           :: [SBool]        -> Int -> SBool
          pbAtLeast          :: [SBool]        -> Int -> SBool
          pbExactly          :: [SBool]        -> Int -> SBool
          pbLe               :: [(Int, SBool)] -> Int -> SBool
          pbGe               :: [(Int, SBool)] -> Int -> SBool
          pbEq               :: [(Int, SBool)] -> Int -> SBool
          pbMutexed          :: [SBool]               -> SBool
          pbStronglyMutexed  :: [SBool]               -> SBool

    These functions, while can be directly coded in SBV, produce better
    translations to SMTLib for more efficient solving of cardinality constraints.
    Currently, only Z3 supports pseudo-booleans directly. For all other solvers,
    SBV will translate these to equivalent terms that do not require special
    functions.

  * The function getModel has been renamed to getAssignment. (The former name is
    now available as a query command.)

  * Export `SolverCapabilities` from `Data.SBV.Internals`, in case users want access.

  * Move code-generation facilities to `Data.SBV.Tools.CodeGen`, no longer exporting
    the relevant functions directly from `Data.SBV`. This could break existing code,
    but the fix should be as simple as `import Data.SBV.Tools.CodeGen`.

  * Move the following two functions to `Data.SBV.Internals`:

         compileToSMTLib
         generateSMTBenchmarks

    If you use them, please `import Data.SBV.Internals`.

  * Reorganized `EqSymbolic` and `EqOrd` classes to collect some of the
    similarly named function together. Users should see no impact due to this change.


### Version 6.0, 2017-05-07

  * This is a backwards compatibility breaking release, hence the major version
    bump from 5.15 to 6.0:

       - Most of existing code should work with no changes.
       - Old code relying on some features might require extra imports,
         since we no longer export some functionality directly from `Data.SBV`.
         This was done in order to reduce the number of exported items to
         avoid extra clutter.
       - Old optimization features are removed, as the new and much improved
         capabilities should be used instead.

  * The next two bullets cover new features in SBV regarding optimization, based
    on the capabilities of the z3 SMT solver. With this release SBV gains the
    capability optimize objectives, and solve MaxSAT problems; by appropriately
    employing the corresponding capabilities in z3. A good review of these features
    as implemented by Z3, and thus what is available in SBV is given in this
    paper: http://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/nbjorner-scss2014.pdf

  * SBV now allows for  real or integral valued metrics. Goals can be lexicographically
    (default), independently, or pareto-front optimized. Currently, only the z3 backend
    supports optimization routines.

    Optimization can be done over bit-vector, real, and integer goals. The relevant
    functions are:

        - `minimize`: Minimize a given arithmetic goal
        - `maximize`: Minimize a given arithmetic goal

    For instance, a call of the form

         minimize "name-of-goal" $ x + 2*y

    Minimizes the arithmetic goal x+2*y, where x and y can be bit-vectors, reals,
    or integers. Such goals will be lexicographically optimized, i.e., in the order
    given. If there are multiple goals, then user can also ask for independent
    optimization results, or pareto-fronts.

    Once the objectives are given, a top level call to `optimize` (similar to `prove`
    and `sat`) performs the optimization.

  * SBV now implements soft-asserts. A soft assertion is a hint to the SMT solver that
    we would like a particular condition to hold if *possible*. That is, if there is
    a solution satisfying it, then we would like it to hold. However, if the set of
    constraints is unsatisfiable, then a soft-assertion can be violated by incurring
    a user-given numeric penalty to satisfy the remaining constraints. The solver then
    tries to minimize the penalty, i.e., satisfy as many of the soft-asserts as possible
    such that the total penalty for those that are not satisfied is minimized.

    Note that `assertSoft` works well with optimization goals (minimize/maximize etc.),
    and are most useful when we are optimizing a metric and thus some of the constraints
    can be relaxed with a penalty to obtain a good solution.

  * SBV no longer provides the old optimization routines, based on iterative and quantifier
    based methods. Those methods were rarely used, and are now superseded by the above
    mechanism. If the old code is needed, please contact for help: They can be resurrected
    in your own code if absolutely necessary.

  * (NB. This feature is deprecated in 7.0, see above for its replacement.)
    SBV now implements tactics, which allow the user to navigate the proof process.
    This is an advanced feature that most users will have no need of, but can become
    handy when dealing with complicated problems. Users can, for instance, implement
    case-splitting in a proof to guide the underlying solver through. Here is the list
    of tactics implemented:

        - `CaseSplit`         : Case-split, with implicit coverage. Bool says whether we should be verbose.
        - `CheckCaseVacuity`  : Should the case-splits be checked for vacuity? (Default: True.)
        - `ParallelCase`      : Run case-splits in parallel. (Default: Sequential.)
        - `CheckConstrVacuity`: Should constraints be checked for vacuity? (Default: False.)
        - `StopAfter`         : Time-out given to solver, in seconds.
        - `CheckUsing`        : Invoke with check-sat-using command, instead of check-sat
        - `UseLogic`          : Use this logic, a custom one can be specified too
        - `UseSolver`         : Use this solver (z3, yices, etc.)
        - `OptimizePriority`  : Specify priority for optimization: Lexicographic (default), Independent, or Pareto.

  * Name-space clean-up. The following modules are no longer automatically exported
    from Data.SBV:

        - `Data.SBV.Tools.ExpectedValue` (computing with expected values)
        - `Data.SBV.Tools.GenTest` (test case generation)
        - `Data.SBV.Tools.Polynomial` (polynomial arithmetic, CRCs etc.)
        - `Data.SBV.Tools.STree` (full symbolic binary trees)

    To use the functionality of these modules, users must now explicitly import the corresponding
    module. Not other changes should be needed other than the explicit import.

  * Changed the signatures of:

          isSatisfiableInCurrentPath :: SBool -> Symbolic Bool
        svIsSatisfiableInCurrentPath :: SVal  -> Symbolic Bool

    to:

          isSatisfiableInCurrentPath :: SBool -> Symbolic (Maybe SatResult)
        svIsSatisfiableInCurrentPath :: SVal  -> Symbolic (Maybe SatResult)

    which returns the result in case of SAT. This is more useful than before. This is
    backwards-compatibility breaking, but is more useful. (Requested by Jared Ziegler.)

  * Add instance `Provable (Symbolic ())`, which simply stands for returning true
    for proof/sat purposes. This allows for simpler coding, as constrain/minimize/maximize
    calls (which return unit) can now be directly sat/prove processed, without needing
    a final call to return at the end.

  * Add type synonym `Goal` (for `Symbolic ()`), in order to simplify type signatures

  * SBV now properly adds check-sat commands and other directives in debugging output.

  * New examples:
      - Data.SBV.Examples.Optimization.LinearOpt: Simple linear-optimization example.
      - Data.SBV.Examples.Optimization.Production: Scheduling machines in a shop
      - Data.SBV.Examples.Optimization.VM: Scheduling virtual-machines in a data-center

### Version 5.15, 2017-01-30

  * Bump up dependency on CrackNum >= 1.9, to get access to hexadecimal floats.
  * Improve time/tracking-print code. Thanks to Iavor Diatchki for the patch.

### Version 5.14, 2017-01-12

  * Bump up QuickCheck dependency to >= 2.9.2 to avoid the following quick-check
    bug <http://github.com/nick8325/quickcheck/issues/113>, which transitively impacted
    the quick-check as implemented by SBV.

  * Generalize casts between integral-floats, using the rounding mode round-nearest-ties-to-even.
    Previously calls to sFromIntegral did not support conversion to floats since it needed
    a rounding mode. But it does make sense to support them with the default mode. If a different
    mode is needed, use the function 'toSFloat' as before, which takes an explicit rounding mode.

### Version 5.13, 2016-10-29

  * Fix broken links, thanks to Stephan Renatus for the patch.

  * Code generation: Create directory path if it does not exist. Thanks to Robert Dockins
    for the patch.

  * Generalize the type of sFromIntegral, dropping the Bits requirement. In turn, this
    allowed us to remove sIntegerToSReal, since sFromIntegral can be used instead.

  * Add support for sRealToSInteger. (Essentially the floor function for SReal.)

  * Several space-leaks fixed for better performance. Patch contributed by Robert Dockins.

  * Improved Random instance for Rational. Thanks to Joe Leslie-Hurd for the idea.

### Version 5.12, 2016-06-06

  * Fix GHC8.0 compilation issues, and warning clean-up. Thanks to Adam Foltzer for the bulk
    of the work and Tom Sydney Kerckhove for the initial patch for 8.0 compatibility.

  * Minor fix to printing models with floats when the base is 2/16, making sure the alignment
    is done properly accommodating for the crackNum output.

  * Wait for external process to die on exception, to avoid spawning zombies. Thanks to
    Daniel Wagner for the patch.

  * Fix hash-consed arrays: Previously we were caching based only on elements, which is not
    sufficient as you can have conflicts differing only on the address type, but same contents.
    Thanks to Brian Huffman for reporting and the corresponding patch.

### Version 5.11, 2016-01-15

  * Fix documentation issue; no functional changes

### Version 5.10, 2016-01-14

  * Documentation: Fix a bunch of dead http links. Thanks to Andres Sicard-Ramirez
    for reporting.

  * Additions to the Dynamic API:

       * svSetBit                  : set a given bit
       * svBlastLE, svBlastBE      : Bit-blast to big/little endian
       * svWordFromLE, svWordFromBE: Unblast from big/little endian
       * svAddConstant             : Add a constant to an SVal
       * svIncrement, svDecrement  : Add/subtract 1 from an SVal

### Version 5.9, 2016-01-05

  * Default definition for 'symbolicMerge', which allows types that are
    instances of 'Generic' to have an automatically derivable merge (i.e.,
    ite) instance. Thanks to Christian Conkle for the patch.

  * Add support for "non-model-vars," where we can now tell SBV not
    to take into account certain variables from a model-building
    perspective. This comes handy in doing an `allSat` calls where
    there might be witness variables that we do not care the uniqueness
    for. See `Data/SBV/Examples/Misc/Auxiliary.hs` for an example, and
    the discussion in http://github.com/LeventErkok/sbv/issues/208 for
    motivation.

  * Yices interface: If Reals are used, then pick the logic QF_UFLRA, instead
    of QF_AUFLIA. Unfortunately, logic selection remains tricky since the SMTLib
    story for logic selection is rather messy. Other solvers are not impacted
    by this change.

### Version 5.8, 2016-01-01

  * Fix some typos
  * Add 'svEnumFromThenTo' to the Dynamic interface, allowing dynamic construction
    of [x, y .. z] and [x .. y] when the involved values are concrete.
  * Add 'svExp' to the Dynamic interface, implementing exponentiation

### Version 5.7, 2015-12-21

  * Export `HasKind(..)` from the Dynamic interface. Thanks to Adam Foltzer for the patch.
  * More careful handling of SMT-Lib reserved names.
  * Update tested version of MathSAT to 5.3.9
  * Generalize `sShiftLeft`/`sShiftRight`/`sRotateLeft`/`sRotateRight` to work with signed
    shift/rotate amounts, where negative values revert the direction. Similar
    generalizations are also done for the dynamic variants.

### Version 5.6, 2015-12-06

  * Minor changes to how we print models:
  * Align by the type
  * Always print the type (previously we were skipping for Bool)

  * Rework how SBV properties are quick-checked; much more usable and robust

  * Provide a function `sbvQuickCheck`, which is essentially the same as
    quickCheck, except it also returns a boolean. Useful for the
    programmable API. (The dynamic version is called `svQuickCheck`.)

  * Several changes/additions in support of the sbvPlugin development:
  * Data.SBV.Dynamic: Define/export `svFloat`/`svDouble`/`sReal`/`sNumerator`/`sDenominator`
  * Data.SBV.Internals: Export constructors of `Result`, `SMTModel`,
    and the function `showModel`
  * Simplify how Uninterpreted-types are internally represented.

### Version 5.5, 2015-11-10

  * This is essentially the same release as 5.4 below, except to allow SBV compile
    with GHC 7.8 series. Thanks to Adam Foltzer for the patch.

### Version 5.4, 2015-11-09

  * Add 'sAssert', which allows users to pepper their code with boolean conditions, much like
    the usual ASSERT calls. Note that the semantics of an 'sAssert' is that it is a NOOP, i.e.,
    it simply returns its final argument. Use in coordination with 'safe' and 'safeWith', see below.

  * Implement 'safe' and 'safeWith', which statically determine all calls to 'sAssert'
    being safe to execute. Any violations will be flagged.

  * SBV->C: Translate 'sAssert' calls to dynamic checks in the generated C code. If this is
    not desired, use the 'cgIgnoreSAssert' function to turn it off.

  * Add 'isSafe': Which converts a 'SafeResult' to a 'Bool', when we are only interested
    in a boolean result.

  * Add Data/SBV/Examples/Misc/NoDiv0 to demonstrate the use of the 'safe' function.

### Version 5.3, 2015-10-20

  * Main point of this release to make SBV compile with GHC 7.8 again, to accommodate mainly
    for Cryptol. As Cryptol moves to GHC >= 7.10, we intend to remove the "compatibility" changes
    again. Thanks to Adam Foltzer for the patch.

  * Minor mods to how bitvector equality/inequality are translated to SMTLib. No user visible
    impact.

### Version 5.2, 2015-10-12

  * Regression on 5.1: Fix a minor bug in base 2/16 printing where uninterpreted constants were
    not handled correctly.

### Version 5.1, 2015-10-10

  * fpMin, fpMax: If these functions receive +0/-0 as their two arguments, i.e., both
    zeros but alternating signs in any order, then SMTLib requires the output to be
    nondeterministically chosen. Previously, we fixed this result as +0 following the
    interpretation in Z3, but Z3 recently changed and now incorporates the nondeterministic
    output. SBV similarly changed to allow for non-determinism here.

  * Change the types of the following Floating-point operations:

        * sFloatAsSWord32, sFloatAsSWord32, blastSFloat, blastSDouble

    These were previously coded as relations, since NaN values were not representable
    in the target domain uniquely. While it was OK, it was hard to use them. We now
    simply implement these as functions, and they are underspecified if the inputs
    are NaNs: In those cases, we simply get a symbolic output. The new types are:

       * sFloatAsSWord32  :: SFloat  -> SWord32
       * sDoubleAsSWord64 :: SDouble -> SWord64
       * blastSFloat      :: SFloat  -> (SBool, [SBool], [SBool])
       * blastSDouble     :: SDouble -> (SBool, [SBool], [SBool])

  * MathSAT backend: Use the SMTLib interpretation of fp.min/fp.max by passing the
    "-theory.fp.minmax_zero_mode=4" argument explicitly.

  * Fix a bug in hash-consing of floating-point constants, where we were confusing +0 and
    -0 since we were using them as keys into the map though they compare equal. We now
    explicitly keep track of the negative-zero status to make sure this confusion does
    not arise. Note that this bug only exhibited itself in rare occurrences of both
    constants being present in a benchmark; a true corner case. Note that @NaN@ values
    are also interesting in this context: Since NaN /= NaN, we never hash-cons floating
    point constants that have the value NaN. But that is actually OK; it is a bit wasteful
    in case you have a lot of NaN constants around, but there is no soundness issue: We
    just waste a little bit of space.

  * Remove the functions `allSatWithAny` and `allSatWithAll`. These two variants do *not*
    make sense when run with multiple solvers, as they internally sequentialize the solutions
    due to the nature of `allSat`. Not really needed anyhow; so removed. The variants
    `satWithAny/All` and `proveWithAny/All` are still available.

  * Export SMTLibVersion from the library, forgotten export needed by Cryptol. Thanks to Adam
    Foltzer for the patch.

  * Slightly modify model-outputs so the variables are aligned vertically. (Only matters
    if we have model-variable names that are of differing length.)

  * Move to Travis-CI "docker" based infrastructure for builds

  * Enable local builds to use the Herbie plugin. Currently SBV does not have any
    expressions that can benefit from Herbie, but it is nice to have this support in general.

### Version 5.0, 2015-09-22

  * Note: This is a backwards-compatibility breaking release, see below for details.

  * SBV now requires GHC 7.10.1 or newer to be compiled, taking advantage of newer features/bug-fixes
    in GHC. If you really need SBV to compile with older GHCs, please get in touch.

  * SBV no longer supports SMTLib1. We now exclusively use SMTLib2 for communicating with backend
    solvers. Strictly speaking, this means some loss in functionality: Uninterpreted-function models
    that we supported via Yices-1 are no longer available. In practice this facility was not really
    used, and required a very old version of Yices that was no longer supported by SRI and has
    lacked in other features. So, in reality this change should hardly matter for end-users.

  * Added function `label`, which is useful in emitting comments around expressions. It is essentially
    a no-op, but does generate a comment with the given text in the SMT-Lib and C output, for diagnostic
    purposes.

  * Added `sFromIntegral`: Conversions from all integral types (SInteger, SWord/SInts) between
    each other. Similar to the `fromIntegral` function of Haskell. These generate simple casts when
    used in code-generation to C, and thus are very efficient.

  * SBV no longer supports the functions sBranch/sAssert, as we realized these functions can cause
    soundness issues under certain conditions. While the triggering scenarios are not common use-cases
    for these functions, we are opting for safety, and thus removing support. See
    http://github.com/LeventErkok/sbv/issues/180 for details; and see below for the new function
    'isSatisfiableInCurrentPath'.

  * A new function 'isSatisfiableInCurrentPath' is added, which checks for satisfiability during a
    symbolic simulation run. This function can be used as the basis of sBranch/sAssert like functionality
    if needed. The difference is that this is a much lower level call, and also exposes the fact that
    the result is in the 'Symbolic' monad (which avoids the soundness issue). Of course, the new type
    makes it less useful as it will not be a drop-in replacement for if-then-else like structure. Intended
    to be used by tools built on top of SBV, as opposed to end-users.

  * SBV no longer implements the 'SignCast' class, as its functionality is replaced by the 'sFromIntegral'
    function. Programs using the functions 'signCast' and 'unsignCast' should simply replace both
    with calls to 'sFromIntegral'. (Note that extra type-annotations might be necessary, similar to
    the uses of the 'fromIntegral' function in Haskell.)

  * Backend solver related changes:

       * Yices: Upgraded to work with Yices release 2.4.1. Note that earlier versions of Yices
         are *not* supported.

       * Boolector: Upgraded to work with new Boolector release 2.0.7. Note that earlier versions
         of Boolector are *not* supported.

       * MathSAT: Upgraded to work with latest release 5.3.7. Note that earlier versions of MathSAT
         are *not* supported (due to a buffering issue in MathSAT itself.)

       * MathSAT: Enabled floating-point support in MathSAT.

  * New examples:

       * Add Data.SBV.Examples.Puzzles.Birthday, which solves the Cheryl-Birthday problem that
         went viral in April 2015. Turns out really easy to solve for SMT, but the formalization
         of the problem is still interesting as an exercise in formal reasoning.

       * Add Data.SBV.Examples.Puzzles.SendMoreMoney, which solves the classic send + more = money
         problem. Really a trivial example, but included since it is pretty much the hello-world for
         basic constraint solving.

       * Add Data.SBV.Examples.Puzzles.Fish, which solves a typical logic puzzle; finding the unique
         solution to a set of assertions made about a bunch of people, their pets, beverage choices,
         etc. Not particularly interesting, but could be fun to play around with for modeling purposes.

       * Add Data.SBV.Examples.BitPrecise.MultMask, which demonstrates the use of the bitvector
         solver to an interesting bit-shuffling problem.

  * Rework floating-point arithmetic, and add missing floating-point operations:

      * fpRem            : remainder
      * fpRoundToIntegral: truncating round
      * fpMin            : min
      * fpMax            : max
      * fpIsEqualObject  : FP equality as object (i.e., NaN equals NaN, +0 does not equal -0, etc.)

    This brings SBV up-to par with everything supported by the SMT-Lib FP theory.

  * Add the IEEEFloatConvertable class, which provides conversions to/from Floats and other types. (i.e.,
    value conversions from all other types to Floats and Doubles; and back.)

  * Add SWord32/SWord64 to/from SFloat/SDouble conversions, as bit-pattern reinterpretation; using the
    IEEE754 interchange format. The functions are: sWord32AsSFloat, sWord64AsSDouble, sFloatAsSWord32,
    sDoubleAsSWord64. Note that the sWord32AsSFloat and sWord64ToSDouble are regular functions, but
    sFloatToSWord32 and sDoubleToSWord64 are "relations", since NaN values are not uniquely convertible.

  * Add 'sExtractBits', which takes a list of indices to extract bits from, essentially
    equivalent to 'map sTestBit'.

  * Rename a set of symbolic functions for consistency. Here are the old/new names:

     * sbvTestBit               --> sTestBit
     * sbvPopCount              --> sPopCount
     * sbvShiftLeft             --> sShiftLeft
     * sbvShiftRight            --> sShiftRight
     * sbvRotateLeft            --> sRotateLeft
     * sbvRotateRight           --> sRotateRight
     * sbvSignedShiftArithRight --> sSignedShiftArithRight

  * Rename all FP recognizers to be in sync with FP operations. Here are the old/new names:

     * isNormalFP       --> fpIsNormal
     * isSubnormalFP    --> fpIsSubnormal
     * isZeroFP         --> fpIsZero
     * isInfiniteFP     --> fpIsInfinite
     * isNaNFP          --> fpIsNaN
     * isNegativeFP     --> fpIsNegative
     * isPositiveFP     --> fpIsPositive
     * isNegativeZeroFP --> fpIsNegativeZero
     * isPositiveZeroFP --> fpIsPositiveZero
     * isPointFP        --> fpIsPoint

  * Lots of other work around floating-point, test cases, reorg, etc.

  * Introduce shorter variants for rounding modes: sRNE, sRNA, sRTP, sRTN, sRTZ;
    aliases for sRoundNearestTiesToEven, sRoundNearestTiesToAway, sRoundTowardPositive,
    sRoundTowardNegative, and sRoundTowardZero; respectively.

### Version 4.4, 2015-04-13

  * Hook-up crackNum package; so counter-examples involving floats and
    doubles can be printed in detail when the printBase is chosen to be
    2 or 16. (With base 10, we still get the simple output.)

      ```
      Prelude Data.SBV> satWith z3{printBase=2} $ \x -> x .== (2::SFloat)
      Satisfiable. Model:
        s0 = 2.0 :: Float
                        3  2          1         0
                        1 09876543 21098765432109876543210
                        S ---E8--- ----------F23----------
                Binary: 0 10000000 00000000000000000000000
                   Hex: 4000 0000
             Precision: SP
                  Sign: Positive
              Exponent: 1 (Stored: 128, Bias: 127)
                 Value: +2.0 (NORMAL)
      ```

  * Change how we print type info; for models instead of SType just print Type (i.e.,
    for SWord8, instead print Word8) which makes more sense and is more consistent.
    This change should be mostly relevant as how we see the counter-example output.

  * Fix long standing bug #75, where we now support arrays with Boolean source/targets.
    This is not a very commonly used case, but by letting the solver pick the logic,
    we now allow arrays to be uniformly supported.

### Version 4.3, 2015-04-10

  * Introduce Data.SBV.Dynamic, by Brian Huffman. This is mostly an internal
    reorg of the SBV codebase, and end-users should not be impacted by the
    changes. The introduction of the Dynamic SBV variant (i.e., one that does
    not mandate a phantom type as in `SBV Word8` etc. allows library writers
    more flexibility as they deal with arbitrary bit-vector sizes. The main
    customer of these changes are the Cryptol language and the associated
    toolset, but other developers building on top of SBV can find it useful
    as well. NB: The "strongly-typed" aspect of SBV is still the main way
    end-users should interact with SBV, and nothing changed in that respect!

  * Add symbolic variants of floating-point rounding-modes for convenience

  * Rename toSReal to sIntegerToSReal, which captures the intent more clearly

  * Code clean-up: remove mbMinBound/mbMaxBound thus allowing less calls to
    unliteral. Contributed by Brian Huffman.

  * Introduce FP conversion functions:

       * Between SReal and SFloat/SDouble
           * fpToSReal
           * sRealToSFloat
           * sRealToSDouble
       * Between SWord32 and SFloat
           * sWord32ToSFloat
           * sFloatToSWord32
       * Between SWord64 and SDouble. (Relational, due to non-unique NaNs)
           * sWord64ToSDouble
       * sDoubleToSWord64
       * From float to sign/exponent/mantissa fields: (Relational, due to non-unique NaNs)
           * blastSFloat
           * blastSDouble

  * Rework floating point classifiers. Remove isSNaN and isFPPoint (both renamed),
    and add the following new recognizers:

       * isNormalFP
       * isSubnormalFP
       * isZeroFP
       * isInfiniteFP
       * isNaNFP
       * isNegativeFP
       * isPositiveFP
       * isNegativeZeroFP
       * isPositiveZeroFP
       * isPointFP (corresponds to a real number, i.e., neither NaN nor infinity)

  * Re-implement sbvTestBit, by Brian Huffman. This version is much faster at large
    word sizes, as it avoids the costly mask generation.

  * Code changes to suppress warnings with GHC7.10. General clean-up.

### Version 4.2, 2015-03-17

  * Add exponentiation (.^). Thanks to Daniel Wagner for contributing the code!

  * Better handling of SBV_$SOLVER_OPTIONS, in particular keeping track of
    proper quoting in environment variables. Thanks to Adam Foltzer for
    the patch!

  * Silence some hlint/ghci warnings. Thanks to Trevor Elliott for the patch!

  * Haddock documentation fixes, improvements, etc.

  * Change ABC default option string to %blast; "&sweep -C 5000; &syn4; &cec -s -m -C 2000"
    which seems to give good results. Use SBV_ABC_OPTIONS environment variable (or
    via abc.rc file and a combination of SBV_ABC_OPTIONS) to experiment.

### Version 4.1, 2015-03-06

  * Add support for the ABC solver from Berkeley. Thanks to Adam Foltzer
    for the required infrastructure! See: https://github.com/berkeley-abc/abc
    And Alan Mishchenko for adding infrastructure to ABC to work with SBV.

  * Upgrade the Boolector connection to use a SMT-Lib2 based interaction. NB. You
    need at least Boolector 2.0.6 installed!

  * Tracking changes in the SMT-Lib floating-point theory. If you are
    using symbolic floating-point types (i.e., SFloat and SDouble), then
    you should upgrade to this version and also get a very latest (unstable)
    Z3 release. See http://smtlib.cs.uiowa.edu/theories-FloatingPoint.shtml
    for details.

  * Introduce a new class, 'RoundingFloat', which supports floating-point
    operations with arbitrary rounding-modes. Note that Haskell only allows
    RoundNearestTiesToAway, but with SBV, we get all 5 IEEE754 rounding-modes
    and all the basic operations ('fpAdd', 'fpMul', 'fpDiv', etc.) with these
    modes.

  * Allow Floating-Point RoundingMode to be symbolic as well

  * Improve the example `Data/SBV/Examples/Misc/Floating.hs` to include
    rounding-mode based addition example.

  * Changes required to make SBV compile with GHC 7.10; mostly around instance
    NFData declarations. Thanks to Iavor Diatchki for the patch.

  * Export a few extra symbols from the Internals module (mainly for
    Cryptol usage.)

### Version 4.0, 2015-01-22

This release mainly contains contributions from Brian Huffman, allowing
end-users to define new symbolic types, such as Word4, that SBV does not
natively support. When GHC gets type-level literals, we shall most likely
incorporate arbitrary bit-sized vectors and ints using this mechanism,
but in the interim, this release provides a means for the users to introduce
individual instances.

  * Modifications to support arbitrary bit-sized vectors;
    These changes have been contributed by Brian Huffman
    of Galois. Thanks Brian.
  * A new example `Data/SBV/Examples/Misc/Word4.hs` showing
    how users can add new symbolic types.
  * Support for rotate-left/rotate-right with variable
    rotation amounts. (From Brian Huffman.)

### Version 3.5, 2015-01-15

This release is mainly adding support for enumerated types in Haskell being
translated to their symbolic counterparts; instead of going completely
uninterpreted.

  * Keep track of data-type details for uninterpreted sorts.
  * Rework the U2Bridge example to use enumerated types.
  * The "Uninterpreted" name no longer makes sense with this change, so
    rework the relevant names to ensure proper internal naming.
  * Add Data/SBV/Examples/Misc/Enumerate.hs as an example for demonstrating
    how enumerations are translated.
  * Fix a long-standing bug in the implementation of select when
    translated as SMT-Lib tables. (Github issue #103.) Thanks to
    Brian Huffman for reporting.

### Version 3.4, 2014-12-21

  * This release is mainly addressing floating-point changes in SMT-Lib.

      * Track changes in the QF_FPA logic standard; new constants and alike. If you are
        using the floating-point logic, then you need a relatively new version of Z3
        installed (4.3.3 or newer).

      * Add unary-negation as an explicit operator. Previously, we merely used the "0-x"
        semantics; but with floating point, this does not hold as 0-0 is 0, and is not -0!
        (Note that negative-zero is a valid floating point value, that is different than
        positive-zero; yet it compares equal to it. Sigh..)

      * Similarly, add abs as a native method; to make sure we map it to fp.abs for
        floating point values.

      * Test suite improvements

### Version 3.3, 2014-12-05

  * Implement 'safe' and 'safeWith', which statically determine all calls to 'sAssert'
    being safe to execute. This way, users can pepper their programs with liberal
    calls to 'sAssert' and check they are all safe in one go without further worry.

  * Robustify the interface to external solvers, by making sure we catch cases where
    the external solver might exist but not be runnable (library dependency missing,
    for example). It is impossible to be absolutely foolproof, but we now catch a
    few more cases and fail gracefully.

### Version 3.2, 2014-11-18

  * Implement 'sAssert'. This adds conditional symbolic simulation, by ensuring arbitrary
    boolean conditions hold during simulation; similar to ASSERT calls in other languages.
    Note that failures will be detected at symbolic-simulation time, i.e., each assert will
    generate a call to the external solver to ensure that the condition is never violated.
    If violation is possible the user will get an error, indicating the failure conditions.

  * Also implement 'sAssertCont' which allows for a programmatic way to extract/display results
    for consumers of 'sAssert'. While the latter simply calls 'error' in case of an assertion
    violation, the 'sAssertCont' variant takes a continuation which can be used to program
    how the results should be interpreted/displayed. (This is useful for libraries built on top of
    SBV.) Note that the type of the continuation is such that execution should still stop, i.e.,
    once an assertion violation is detected, symbolic simulation will never continue.

  * Rework/simplify the 'Mergeable' class to make sure 'sBranch' is sufficiently lazy
    in case of structural merges. The original implementation was only
    lazy at the Word instance, but not at lists/tuples etc. Thanks to Brian Huffman
    for reporting this bug.

  * Add a few constant-folding optimizations for 'sDiv' and 'sRem'

  * Boolector: Modify output parser to conform to the new Boolector output format. This
    means that you need at least v2.0.0 of Boolector installed if you want to use that
    particular solver.

  * Fix long-standing translation bug regarding boolean Ord class comparisons. (i.e.,
    'False > True' etc.) While Haskell allows for this, SMT-Lib does not; and hence
    we have to be careful in translating. Thanks to Brian Huffman for reporting.

  * C code generation: Correctly translate square-root and fusedMA functions to C.

### Version 3.1, 2014-07-12

 NB: GHC 7.8.1 and 7.8.2 has a serious bug <http://ghc.haskell.org/trac/ghc/ticket/9078>
     that causes SBV to crash under heavy/repeated calls. The bug is addressed
     in GHC 7.8.3; so upgrading to GHC 7.8.3 is essential for using SBV!

 New features/bug-fixes in v3.1:

 * Using multiple-SMT solvers in parallel:
      * Added functions that let the user run multiple solvers, using asynchronous
        threads. All results can be obtained (proveWithAll, proveWithAny, satWithAll),
        or SBV can return the fastest result (satWithAny, allSatWithAll, allSatWithAny).
        These functions are good for playing with multiple-solvers, especially on
        machines with multiple-cores.
      * Add function: sbvAvailableSolvers; which returns the list of solvers currently
        available, as installed on the machine we are running. (Not the list that SBV
        supports, but those that are actually available at run-time.) This function
        is useful with the multi-solve API.
 * Implement sBranch:
      * sBranch is a variant of 'ite' that consults the external
        SMT solver to see if a given branch condition is satisfiable
        before evaluating it. This can make certain otherwise recursive
        and thus not-symbolically-terminating inputs amenable to symbolic
        simulation, if termination can be established this way. Needless
        to say, this problem is always decidable as far as SBV programs
        are concerned, but it does not mean the decision procedure is cheap!
        Use with care.
      * sBranchTimeOut config parameter can be used to curtail long runs when
        sBranch is used. Of course, if time-out happens, SBV will
        assume the branch is feasible, in which case symbolic-termination
        may come back to bite you.)
 * New API:
      * Add predicate 'isSNaN' which allows testing 'SFloat'/'SDouble' values
        for nan-ness. This is similar to the Prelude function 'isNaN', except
        the Prelude version requires a RealFrac instance, which unfortunately is
        not currently implementable for cases. (Requires trigonometric functions etc.)
        Thus, we provide 'isSNaN' separately (along with the already existing
        'isFPPoint') to simplify reasoning with floating-point.
 * Examples:
     * Add Data/SBV/Examples/Misc/SBranch.hs, to illustrate the use of sBranch.
 * Bug fixes:
     * Fix pipe-blocking issue, which exhibited itself in the presence of
       large numbers of variables (> 10K or so). See github issue #86. Thanks
       to Philipp Meyer for the fine report.
 * Misc:
     * Add missing SFloat/SDouble instances for SatModel class
     * Explicitly support KBool as a kind, separating it from `KUnbounded False 1`.
       Thanks to Brian Huffman for contributing the changes. This should have no
       user-visible impact, but comes in handy for internal reasons.

### Version 3.0, 2014-02-16

 * Support for floating-point numbers:
      * Preliminary support for IEEE-floating point arithmetic, introducing
        the types `SFloat` and `SDouble`. The support is still quite new,
        and Z3 is the only solver that currently features a solver for
        this logic. Likely to have bugs, both at the SBV level, and at the
        Z3 level; so any bug reports are welcome!
 * New backend solvers:
      * SBV now supports MathSAT from Fondazione Bruno Kessler and
        DISI-University of Trento. See: http://mathsat.fbk.eu/
 * Support all-sat calls in the presence of uninterpreted sorts:
      * Implement better support for `allSat` in the presence of uninterpreted
        sorts. Previously, SBV simply rejected running `allSat` queries
        in the presence of uninterpreted sorts, since it was not possible
        to generate a refuting model. The model returned by the SMT solver
        is simply not usable, since it names constants that is not visible
        in a subsequent run. Eric Seidel came up with the idea that we can
        actually compute equivalence classes based on a produced model, and
        assert the constraint that the new model should disallow the previously
        found equivalence classes instead. The idea seems to work well
        in practice, and there is also an example program demonstrating
        the functionality: Examples/Uninterpreted/UISortAllSat.hs
 * Programmable model extraction improvements:
      * Add functions `getModelDictionary` and `getModelDictionaries`, which
        provide low-level access to models returned from SMT solvers. Former
        for `sat` and `prove` calls, latter for `allSat` calls. Together with
        the exported utils from the `Data.SBV.Internals` module, this should
        allow for expert users to dissect the models returned and do fancier
        programming on top of SBV.
      * Add `getModelValue`, `getModelValues`, `getModelUninterpretedValue`, and
        `getModelUninterpretedValues`; which further aid in model value
        extraction.
 * Other:
      * Allow users to specify the SMT-Lib logic to use, if necessary. SBV will
        still pick the logic automatically, but users can now override that choice.
        Comes in handy when playing with custom logics.
 * Bug fixes:
      * Address allsat-laziness issue (#78 in github issue tracker). Essentially,
        simplify how all-sat is called so we can avoid calling the solver for
        solutions that are not needed. Thanks to Eric Seidel for reporting.
 * Examples:
      * Add Data/SBV/Examples/Misc/ModelExtract.hs as a simple example for
        programmable model extraction and usage.
      * Add Data/SBV/Examples/Misc/Floating.hs for some FP examples.
      * Use the AUFLIA logic in Examples.Existentials.Diophantine which helps
        z3 complete the proof quickly. (The BV logics take too long for this problem.)

### Version 2.10, 2013-03-22

 * Add support for the Boolector SMT solver
    * See: https://boolector.github.io
    * Use `import Data.SBV.Bridge.Boolector` to use Boolector from SBV
    * Boolector supports QF_BV (with an without arrays). In the last
      SMT-Lib competition it won both bit-vector categories. It is definitely
      worth trying it out for bitvector problems.
 * Changes to the library:
    * Generalize types of `allDifferent` and `allEqual` to take
      arbitrary EqSymbolic values. (Previously was just over SBV values.)
    * Add `inRange` predicate, which checks if a value is bounded within
      two others.
    * Add `sElem` predicate, which checks for symbolic membership
    * Add `fullAdder`: Returns the carry-over as a separate boolean bit.
    * Add `fullMultiplier`: Returns both the lower and higher bits resulting
      from  multiplication.
    * Use the SMT-Lib Bool sort to represent SBool, instead of bit-vectors of length 1.
      While this is an under-the-hood mechanism that should be user-transparent, it
      turns out that one can no longer write axioms that return booleans in a direct
      way due to this translation. This change makes it easier to write axioms that
      utilize booleans as there is now a 1-to-1 match. (Suggested by Thomas DuBuisson.)
 * Solvers changes:
    * Z3: Update to the new parameter naming schema of Z3. This implies that
      you need to have a really recent version of Z3 installed, something
      in the Z3-4.3 series.
 * Examples:
    * Add Examples/Uninterpreted/Shannon.hs: Demonstrating Shannon expansion,
      boolean derivatives, etc.
 * Bug-fixes:
    * Gracefully handle the case if the backend-SMT solver does not put anything
      in stdout. (Reported by Thomas DuBuisson.)
    * Handle uninterpreted sort values, if they happen to be only created via
      function calls, as opposed to being inputs. (Reported by Thomas DuBuisson.)

### Version 2.9, 2013-01-02

  * Add support for the CVC4 SMT solver from Stanford: <https://cvc4.github.io/>
    NB. Z3 remains the default solver for SBV. To use CVC4, use the
    *With variants of the interface (i.e., proveWith, satWith, ..)
    by passing cvc4 as the solver argument. (Similarly, use 'yices'
    as the argument for the *With functions for invoking yices.)
  * Latest release of Yices calls the SMT-Lib based solver executable
    yices-smt. Updated the default value of the executable to have this
    name for ease of use.
  * Add an extra boolean flag to compileToSMTLib and generateSMTBenchmarks
    functions to control if the translation should keep the query as is
    (for SAT cases), or negate it (for PROVE cases). Previously, this value
    was hard-coded to do the PROVE case only.
  * Add bridge modules, to simplify use of different solvers. You can now say:

          import Data.SBV.Bridge.CVC4
          import Data.SBV.Bridge.Yices
          import Data.SBV.Bridge.Z3

    to pick the appropriate default solver. if you simply 'import Data.SBV', then
    you will get the default SMT solver, which is currently Z3. The value
    'defaultSMTSolver' refers to z3 (currently), and 'sbvCurrentSolver' refers
    to the chosen solver as determined by the imported module. (The latter is
    useful for modifying options to the SMT solver in an solver-agnostic way.)
  * Various improvements to Z3 model parsing routines.

### Version 2.8, 2012-11-29

  * Rename the SNum class to SIntegral, and make it index over regular
    types. This makes it much more useful, simplifying coding of
    polymorphic symbolic functions over integral types, which is
    the common case.
  * Add the functions:
  * sbvShiftLeft
  * sbvShiftRight
    which can accommodate unsigned symbolic shift amounts. Note that
    one cannot use the Haskell shiftL/shiftR functions from the Bits class since
    they are hard-wired to take 'Int' values as the shift amounts only.
  * Add a new function 'sbvArithShiftRight', which is the same as
    a shift-right, except it uses the MSB of the input as the bit to fill
    in (instead of always filling in with 0 bits). Note that this is
    the same as shiftRight for signed values, but differs from a shiftRight
    when the input is unsigned. (There is no Haskell analogue of this
    function, as Haskell shiftR is always arithmetic for signed
    types and logical for unsigned ones.) This variant is designed for
    use cases when one uses the underlying unsigned SMT-Lib representation
    to implement custom signed operations, for instance.
  * Several typo fixes.

### Version 2.7, 2012-10-21

  * Add missing QuickCheck instance for SReal
  * When dealing with concrete SReals, make sure to operate
    only on exact algebraic reals on the Haskell side, leaving
    true algebraic reals (i.e., those that are roots of polynomials
    that cannot be expressed as a rational) symbolic. This avoids
    issues with functions that we cannot implement directly on
    the Haskell side, like exact square-roots.
  * Documentation tweaks, typo fixes etc.
  * Rename BVDivisible class to SDivisible; since SInteger
    is also an instance of this class, and SDivisible is a
    more appropriate name to start with. Also add sQuot and sRem
    methods; along with sDivMod, sDiv, and sMod, with usual
    semantics.
  * Improve test suite, adding many constant-folding tests
    and start using cabal based tests (--enable-tests option.)

### Versions 2.4, 2.5, and 2.6: Around mid October 2012

  * Workaround issues related hackage compilation, in particular to the
    problem with the new containers package release, which does provide
    an NFData instance for sequences.
  * Add explicit Num requirements when necessary, as the Bits class
    no longer does this.
  * Remove dependency on the hackage package strict-concurrency, as
    hackage can no longer compile it due to some dependency mismatch.
  * Add forgotten Real class instance for the type 'AlgReal'
  * Stop putting bounds on hackage dependencies, as they cause
    more trouble then they actually help. (See the discussion
    here: <http://www.haskell.org/pipermail/haskell-cafe/2012-July/102352.html>.)

### Version 2.3, 2012-07-20

  * Maintenance release, no new features.
  * Tweak cabal dependencies to avoid using packages that are newer
    than those that come with ghc-7.4.2. Apparently this is a no-no
    that breaks many things, see the discussion in this thread:
      http://www.haskell.org/pipermail/haskell-cafe/2012-July/102352.html
    In particular, the use of containers >= 0.5 is *not* OK until we have
    a version of GHC that comes with that version.

### Version 2.2, 2012-07-17

  * Maintenance release, no new features.
  * Update cabal dependencies, in particular fix the
    regression with respect to latest version of the
    containers package.

### Version 2.1, 2012-05-24

 * Library:
    * Add support for uninterpreted sorts, together with user defined
      domain axioms. See Data.SBV.Examples.Uninterpreted.Sort
      and Data.SBV.Examples.Uninterpreted.Deduce for basic examples of
      this feature.
    * Add support for C code-generation with SReals. The user picks
      one of 3 possible C types for the SReal type: CgFloat, CgDouble
      or CgLongDouble, using the function cgSRealType. Naturally, the
      resulting C program will suffer a loss of precision, as it will
      be subject to IEE-754 rounding as implied by the underlying type.
    * Add toSReal :: SInteger -> SReal, which can be used to promote
      symbolic integers to reals. Comes handy in mixed integer/real
      computations.
 * Examples:
    * Recast the dog-cat-mouse example to use the solver over reals.
    * Add Data.SBV.Examples.Uninterpreted.Sort, and
           Data.SBV.Examples.Uninterpreted.Deduce
      for illustrating uninterpreted sorts and axioms.

### Version 2.0, 2012-05-10

  This is a major release of SBV, adding support for symbolic algebraic reals: SReal.
  See http://en.wikipedia.org/wiki/Algebraic_number for details. In brief, algebraic
  reals are solutions to univariate polynomials with rational coefficients. The arithmetic
  on algebraic reals is precise, with no approximation errors. Note that algebraic reals
  are a proper subset of all reals, in particular transcendental numbers are not
  representable in this way. (For instance, "sqrt 2" is algebraic, but pi, e are not.)
  However, algebraic reals is a superset of rationals, so SBV now also supports symbolic
  rationals as well.

  You *should* use Z3 v4.0 when working with real numbers. While the interface will
  work with older versions of Z3 (or other SMT solvers in general), it uses Z3
  root-obj construct to retrieve and query algebraic reals.

  While SReal values have infinite precision, printing such values is not trivial since
  we might need an infinite number of digits if the result happens to be irrational. The
  user controls printing precision, by specifying how many digits after the decimal point
  should be printed. The default number of decimal digits to print is 10. (See the
  'printRealPrec' field of SMT-solver configuration.)

  The acronym SBV used to stand for Symbolic Bit Vectors. However, SBV has grown beyond
  bit-vectors, especially with the addition of support for SInteger and SReal types and
  other code-generation utilities. Therefore, "SMT Based Verification" is now a better fit
  for the expansion of the acronym SBV.

  Other notable changes in the library:

  * Add functions s[TYPE] and s[TYPE]s for each symbolic type we support (i.e.,
    sBool, sBools, sWord8, sWord8s, etc.), to create symbolic variables of the
    right kind.  Strictly speaking these are just synonyms for 'free'
    and 'mapM free' (plural versions), so they are not adding any additional
    power. Except, they are specialized at their respective types, and might be
    easier to remember.
  * Add function solve, which is merely a synonym for (return . bAnd), but
    it simplifies expressing problems.
  * Add class SNum, which simplifies writing polymorphic code over symbolic values
  * Increase haddock coverage metrics
  * Major code refactoring around symbolic kinds
  * SMTLib2: Emit ":produce-models" call before setting the logic, as required
    by the SMT-Lib2 standard. [Patch provided by arrowdodger on github, thanks!]

  Bugs fixed:

   * [Performance] Use a much simpler default definition for "select": While the
     older version (based on binary search on the bits of the indexer) was correct,
     it created unnecessarily big expressions. Since SBV does not have a notion
     of concrete subwords, the binary-search trick was not bringing any advantage
     in any case. Instead, we now simply use a linear walk over the elements.

  Examples:

   * Change dog-cat-mouse example to use SInteger for the counts
   * Add merge-sort example: Data.SBV.Examples.BitPrecise.MergeSort
   * Add diophantine solver example: Data.SBV.Examples.Existentials.Diophantine

### Version 1.4, 2012-05-10

   * Interim release for test purposes

### Version 1.3, 2012-02-25

  * Workaround cabal/hackage issue, functionally the same as release
    1.2 below

### Version 1.2, 2012-02-25

 Library:

  * Add a hook so users can add custom script segments for SMT solvers. The new
    "solverTweaks" field in the SMTConfig data-type can be used for this purpose.
    The need for this came about due to the need to workaround a Z3 v3.2 issue
    detailed below:
      http://stackoverflow.com/questions/9426420/soundness-issue-with-integer-bv-mixed-benchmarks
    As a consequence, mixed Integer/BV problems can cause soundness issues in Z3
    and does in SBV. Unfortunately, it is too severe for SBV to add the workaround
    option, as it slows down the solver as a side effect as well. Thus, we are
    making this optionally available if/when needed. (Note that the work-around
    should not be necessary with Z3 v3.3; which is not released yet.)
  * Other minor clean-up

### Version 1.1, 2012-02-14

 Library:

  * Rename bitValue to sbvTestBit
  * Add sbvPopCount
  * Add a custom implementation of 'popCount' for the Bits class
    instance of SBV (GHC >= 7.4.1 only)
  * Add 'sbvCheckSolverInstallation', which can be used to check
    that the given solver is installed and good to go.
  * Add 'generateSMTBenchmarks', simplifying the generation of
    SMTLib benchmarks for offline sharing.

### Version 1.0, 2012-02-13

 Library:

  * Z3 is now the "default" SMT solver. Yices is still available, but
    has to be specifically selected. (Use satWith, allSatWith, proveWith, etc.)
  * Better handling of the pConstrain probability threshold for test
    case generation and quickCheck purposes.
  * Add 'renderTest', which accompanies 'genTest' to render test
    vectors as Haskell/C/Forte program segments.
  * Add 'expectedValue' which can compute the expected value of
    a symbolic value under the given constraints. Useful for statistical
    analysis and probability computations.
  * When saturating provable values, use forAll_ for proofs and forSome_
    for sat/allSat. (Previously we were always using forAll_, which is
    not incorrect but less intuitive.)
  * add function:
      extractModels :: SatModel a => AllSatResult -> [a]
    which simplifies accessing allSat results greatly.

 Code-generation:

  * add "cgGenerateMakefile" which allows the user to choose if SBV
    should generate a Makefile. (default: True)

 Other

  * Changes to make it compile with GHC 7.4.1.

### Version 0.9.24, 2011-12-28

  Library:

   * Add "forSome," analogous to "forAll." (The name "exists" would've
     been better, but it's already taken.) This is not as useful as
     one might think as forAll and forSome do not nest, as an inner
     application of one pushes its argument to a Predicate, making
     the outer one useless, but it is nonetheless useful by itself.
   * Add a "Modelable" class, which simplifies model extraction.
   * Add support for quick-check at the "Symbolic SBool" level. Previously
     SBV only allowed functions returning SBool to be quick-checked, which
     forced a certain style of coding. In particular with the addition
     of quantifiers, the new coding style mostly puts the top-level
     expressions in the Symbolic monad, which were not quick-checkable
     before. With new support, the quickCheck, prove, sat, and allSat
     commands are all interchangeable with obvious meanings.
   * Add support for concrete test case generation, see the genTest function.
   * Improve optimize routines and add support for iterative optimization.
   * Add "constrain", simplifying conjunctive constraints, especially
     useful for adding constraints at variable generation time via
     forall/exists. Note that the interpretation of such constraints
     is different for genTest and quickCheck functions, where constraints
     will be used for appropriately filtering acceptable test values
     in those two cases.
   * Add "pConstrain", which probabilistically adds constraints. This
     is useful for quickCheck and genTest functions for filtering acceptable
     test values. (Calls to pConstrain will be rejected for sat/prove calls.)
   * Add "isVacuous" which can be used to check that the constraints added
     via constrain are satisfiable. This is useful to prevent vacuous passes,
     i.e., when a proof is not just passing because the constraints imposed
     are inconsistent. (Also added accompanying isVacuousWith.)
   * Add "free" and "free_", analogous to "forall/forall_" and "exists/exists_"
     The difference is that free behaves universally in a proof context, while
     it behaves existentially in a sat context. This allows us to express
     properties more succinctly, since the intended semantics is usually this
     way depending on the context. (i.e., in a proof, we want our variables
     universal, in a sat call existential.) Of course, exists/forall are still
     available when mixed quantifiers are needed, or when the user wants to
     be explicit about the quantifiers.

  Examples

   * Add Data/SBV/Examples/Puzzles/Coins.hs. (Shows the usage of "constrain".)

  Dependencies

   * Bump up random package dependency to 1.0.1.1 (from 1.0.0.2)

  Internal

   * Major reorganization of files to and build infrastructure to
     decrease build times and better layout
   * Get rid of custom Setup.hs, just use simple build. The extra work
     was not worth the complexity.

### Version 0.9.23, 2011-12-05

  Library:

   * Add support for SInteger, the type of signed unbounded integer
     values. SBV can now prove theorems about unbounded numbers,
     following the semantics of Haskell Integer type. (Requires z3 to
     be used as the backend solver.)
   * Add functions 'optimize', 'maximize', and 'minimize' that can
     be used to find optimal solutions to given constraints with
     respect to a given cost function.
   * Add 'cgUninterpret', which simplifies code generation when we want
     to use an alternate definition in the target language (i.e., C). This
     is important for efficient code generation, when we want to
     take advantage of native libraries available in the target platform.

  Other:

   * Change getModel to return a tuple in the success case, where
     the first component is a boolean indicating whether the model
     is "potential." This is used to indicate that the solver
     actually returned "unknown" for the problem and the model
     might therefore be bogus. Note that we did not need this before
     since we only supported bounded bit-vectors, which has a decidable
     theory. With the addition of unbounded Integers and quantifiers, the
     solvers can now return unknown. This should still be rare in practice,
     but can happen with the use of non-linear constructs. (i.e.,
     multiplication of two variables.)

### Version 0.9.22, 2011-11-13

  The major change in this release is the support for quantifiers. The
  SBV library *no* longer assumes all variables are universals in a proof,
  (and correspondingly existential in a sat) call. Instead, the user
  marks free-variables appropriately using forall/exists functions, and the
  solver translates them accordingly. Note that this is a non-backwards
  compatible change in sat calls, as the semantics of formulas is essentially
  changing. While this is unfortunate, it is more uniform and simpler to understand
  in general.

  This release also adds support for the Z3 solver, which is the main
  SMT-solver used for solving formulas involving quantifiers. More formally,
  we use the new AUFBV/ABV/UFBV logics when quantifiers are involved. Also,
  the communication with Z3 is now done via SMT-Lib2 format. Eventually
  the SMTLib1 connection will be severed.

  The other main change is the support for C code generation with
  uninterpreted functions enabling users to interface with external
  C functions defined elsewhere. See below for details.

  Other changes:

  Code:

   * Change getModel, so it returns an Either value to indicate
     something went wrong; instead of throwing an error
   * Add support for computing CRCs directly (without needing
     polynomial division).

  Code generation:

   * Add "cgGenerateDriver" function, which can be used to turn
     on/off driver program generation. Default is to generate
     a driver. (Issue "cgGenerateDriver False" to skip the driver.)
     For a library, a driver will be generated if any of the
     constituent parts has a driver. Otherwise it will be skipped.
   * Fix a bug in C code generation where "Not" over booleans were
     incorrectly getting translated due to need for masking.
   * Add support for compilation with uninterpreted functions. Users
     can now specify the corresponding C code and SBV will simply
     call the "native" functions instead of generating it. This
     enables interfacing with other C programs. See the functions:
     cgAddPrototype, cgAddDecl, cgAddLDFlags

  Examples:

   * Add CRC polynomial generation example via existentials
   * Add USB CRC code generation example, both via polynomials and using the internal CRC functionality

### Version 0.9.21, 2011-08-05

 Code generation:

  * Allow for inclusion of user makefiles
  * Allow for CCFLAGS to be set by the user
  * Other minor clean-up

### Version 0.9.20, 2011-06-05

  Regression on 0.9.19; add missing file to cabal

### Version 0.9.19, 2011-06-05


  * Add SignCast class for conversion between signed/unsigned
    quantities for same-sized bit-vectors
  * Add full-binary trees that can be indexed symbolically (STree). The
    advantage of this type is that the reads and writes take
    logarithmic time. Suitable for implementing faster symbolic look-up.
  * Expose HasSignAndSize class through Data.SBV.Internals
  * Many minor improvements, file re-orgs

Examples:

  * Add sentence-counting example
  * Add an implementation of RC4

### Version 0.9.18, 2011-04-07

Code:

  * Re-engineer code-generation, and compilation to C.
    In particular, allow arrays of inputs to be specified,
    both as function arguments and output reference values.
  * Add support for generation of generation of C-libraries,
    allowing code generation for a set of functions that
    work together.

Examples:

  * Update code-generation examples to use the new API.
  * Include a library-generation example for doing 128-bit
    AES encryption

### Version 0.9.17, 2011-03-29

Code:

  * Simplify and reorganize the test suite

Examples:

  * Improve AES decryption example, by using
    table-lookups in InvMixColumns.

### Version 0.9.16, 2011-03-28

Code:

  * Further optimizations on Bits instance of SBV

Examples:

  * Add AES algorithm as an example, showing how
    encryption algorithms are particularly suitable
    for use with the code-generator

### Version 0.9.15, 2011-03-24

Bug fixes:

  * Fix rotateL/rotateR instances on concrete
    words. Previous versions was bogus since
    it relied on the Integer instance, which
    does the wrong thing after normalization.
  * Fix conversion of signed numbers from bits,
    previous version did not handle twos
    complement layout correctly

Testing:

  * Add a sleuth of concrete test cases on
    arithmetic to catch bugs. (There are many
    of them, ~30K, but they run quickly.)

### Version 0.9.14, 2011-03-19

  * Re-implement sharing using Stable names, inspired
    by the Data.Reify techniques. This avoids tricks
    with unsafe memory stashing, and hence is safe.
    Thus, issues with respect to CAFs are now resolved.

### Version 0.9.13, 2011-03-16

Bug fixes:

  * Make sure SBool short-cut evaluations are done
    as early as possible, as these help with coding
    recursion-depth based algorithms, when dealing
    with symbolic termination issues.

Examples:

  * Add fibonacci code-generation example, original
    code by Lee Pike.
  * Add a GCD code-generation/verification example

### Version 0.9.12, 2011-03-10

New features:

  * Add support for compilation to C
  * Add a mechanism for offline saving of SMT-Lib files

Bug fixes:

  * Output naming bug, reported by Josef Svenningsson
  * Specification bug in Legatos multiplier example

### Version 0.9.11, 2011-02-16

  * Make ghc-7.0 happy, minor re-org on the cabal file/Setup.hs

### Version 0.9.10, 2011-02-15

  * Integrate commits from Iavor: Generalize SBVs to keep
    track the integer directly without resorting to different
    leaf types
  * Remove the unnecessary CLC instruction from the Legato example
  * More tests

### Version 0.9.9, 2011-01-23

  * Support for user-defined SMT-Lib axioms to be
    specified for uninterpreted constants/functions
  * Move to using doctest style inline tests

### Version 0.9.8, 2011-01-22

  * Better support for uninterpreted-functions
  * Support counter-examples with SArrays
  * Ladner-Fischer scheme example
  * Documentation updates

### Version 0.9.7, 2011-01-18

  * First stable public hackage release

### Versions 0.0.0 - 0.9.6, Mid 2010 through early 2011

  * Basic infrastructure, design exploration
