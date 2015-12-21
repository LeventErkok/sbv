* Hackage: <http://hackage.haskell.org/package/sbv>
* GitHub:  <http://leventerkok.github.com/sbv/>

* Latest Hackage released version: 5.7, 2015-12-21

### Version 5.7, 2015-12-21

  * Export HasKind(..) from the Dynamic interface. Thanks to Adam Foltzer for the patch.
  * More careful handling of SMT-Lib reserved names.
  * Update tested version of MathSAT to 5.3.9
  * Generalize sShiftLeft/sShiftRight/sRotateLeft/sRotateRight to work with signed
    shift/rotate amounts, where negative values revert the direction. Similar
    generalizations are also done for the dynamic variants.

### Version 5.6, 2015-12-06
  
  * Minor changes to how we print models:
  	* Align by the type
  	* Always print the type (previously we were skipping for Bool)

  * Rework how SBV properties are quick-checked; much more usable and robust

  * Provide a function sbvQuickCheck, which is essentially the same as
    quickCheck, except it also returns a boolean. Useful for the
    programmable API. (The dynamic version is called svQuickCheck)

  * Several changes/additions in support of the sbvPlugin development:
  	* Data.SBV.Dynamic: Define/export svFloat/svDouble/sReal/sNumerator/sDenominator
	* Data.SBV.Internals: Export constructors of Result, SMTModel,
	  and the function showModel
	* Simplify how Uninterpreted-types are internally represented.

### Version 5.5, 2015-11-10

  * This is essentially the same release as 5.4 below, except to allow SBV compile
    with GHC 7.8 series. Thanks to Adam Foltzer for the patch.

### Version 5.4, 2015-11-09

  * Add 'sAssert', which allows users to pepper their code with boolean conditions, much like
    the usual ASSERT calls. Note that the semantics of an 'sAssert' is that it is a NOOP, i.e.,
    it simply returns its final argument. Use in coordination with 'safe' and 'safeWith', see below.

  * Implement 'safe' and 'safeWith', which statically determine all calls to 'sAssert'
    being safe to execute. Any vilations will be flagged. 

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
    nondeterministicly chosen. Previously, we fixed this result as +0 following the
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

  * Added function "label", which is useful in emitting comments around expressions. It is essentially
    a no-op, but does generate a comment with the given text in the SMT-Lib and C output, for diagnostic
    purposes.

  * Added "sFromIntegral": Conversions from all integral types (SInteger, SWord/SInts) between
    each other. Similar to the "fromIntegral" function of Haskell. These generate simple casts when
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
      * fpMin		 : min
      * fpMax		 : max
      * fpIsEqualObject	 : FP equality as object (i.e., NaN equals NaN, +0 does not equal -0, etc.)

    This brings SBV up-to par with everything supported by the SMT-Lib FP theory.

  * Add the IEEEFloatConvertable class, which provides conversions to/from Floats and other types. (i.e.,
    value conversions from all other types to Floats and Doubles; and back.)

  * Add SWord32/SWord64 to/from SFloat/SDouble conversions, as bit-pattern reinterpretation; using the
    IEEE754 interchange format. The functions are: sWord32AsSFloat, sWord64AsSDouble, sFloatAsSWord32,
    sDoubleAsSWord64. Note that the sWord32AsSFloat and sWord64ToSDouble are regular functions, but
    sFloatToSWord32 and sDoubleToSWord64 are "relations", since NaN values are not uniquely convertable.

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

  * Change how we print type info; for models insted of SType just print Type (i.e.,
    for SWord8, instead print Word8) which makes more sense and is more consistent.
    This change should be mostly relevant as how we see the counter-example output.

  * Fix long standing bug #75, where we now support arrays with Boolean source/targets.
    This is not a very commonly used case, but by letting the solver pick the logic,
    we now allow arrays to be uniformly supported.

### Version 4.3, 2015-04-10

  * Introduce Data.SBV.Dynamic, by Brian Huffman. This is mostly an internal
    reorg of the SBV codebase, and end-users should not be impacted by the
    changes. The introduction of the Dynamic SBV variant (i.e., one that does
    not mandate a phantom type as in "SBV Word8" etc. allows library writers
    more flexibility as they deal with arbitrary bit-vector sizes. The main
    customor of these changes are the Cryptol language and the associated
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

  * Reimplement sbvTestBit, by Brian Huffman. This version is much faster at large
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
    for the required infrastructure! See: http://www.eecs.berkeley.edu/~alanmi/abc/
    And Alan Mishchenko for adding infrastructure to ABC to work with SBV.

  * Upgrade the Boolector connection to use a SMT-Lib2 based interaction. NB. You
    need at least Boolector 2.0.6 installed!

  * Tracking changes in the SMT-Lib floating-point theory. If you are
    using symbolic floating-point types (i.e., SFloat and SDouble), then
    you should upgrade to this version and also get a very latest (unstable)
    Z3 release. See http://smtlib.cs.uiowa.edu/theories/FloatingPoint.smt2
    for details.

  * Introduce a new class, 'RoundingFloat', which supports floating-point
    operations with arbitrary rounding-modes. Note that Haskell only allows
    RoundNearestTiesToAway, but with SBV, we get all 5 IEEE754 rounding-modes
    and all the basic operations ('fpAdd', 'fpMul', 'fpDiv', etc.) with these
    modes.
    
  * Allow Floating-Point RoundingMode to be symbolic as well

  * Improve the example "Data/SBV/Examples/Misc/Floating.hs" to include
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
    of Galois.. Thanks Brian.
  * A new example "Data/SBV/Examples/Misc/Word4.hs" showing
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

  * Add a few constant-folding optimizations for 'sDiv'and 'sRem'

  * Boolector: Modify output parser to conform to the new Boolector output format. This
    means that you need at least v2.0.0 of Boolector installed if you want to use that
    particular solver.

  * Fix long-standing translation bug regarding boolean Ord class comparisons. (i.e., 
    'False > True' etc.) While Haskell allows for this, SMT-Lib does not; and hence
    we have to be careful in translating. Thanks to Brian Huffman for reporting.

  * C code generation: Correctly translate square-root and fusedMA functions to C.

### Version 3.1, 2014-07-12
 
 NB: GHC 7.8.1 and 7.8.2 has a serious bug (https://ghc.haskell.org/trac/ghc/ticket/9078)
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
	before evaluating it. This can make certain "otherwise recursive
	and thus not-symbolically-terminating inputs" amenable to symbolic
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
     * Explicitly support KBool as a kind, separating it from "KUnbounded False 1".
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
    * See: http://fmv.jku.at/boolector/
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

  - Add support for the CVC4 SMT solver from New York University and
    the University of Iowa. (http://cvc4.cs.nyu.edu/).
    NB. Z3 remains the default solver for SBV. To use CVC4, use the
    *With variants of the interface (i.e., proveWith, satWith, ..)
    by passing cvc4 as the solver argument. (Similarly, use 'yices'
    as the argument for the *With functions for invoking yices.)
  - Latest release of Yices calls the SMT-Lib based solver executable
    yices-smt. Updated the default value of the executable to have this
    name for ease of use.
  - Add an extra boolean flag to compileToSMTLib and generateSMTBenchmarks
    functions to control if the translation should keep the query as is
    (for SAT cases), or negate it (for PROVE cases). Previously, this value
    was hard-coded to do the PROVE case only.
  - Add bridge modules, to simplify use of different solvers. You can now say:

          import Data.SBV.Bridge.CVC4
          import Data.SBV.Bridge.Yices
          import Data.SBV.Bridge.Z3
   
    to pick the appropriate default solver. if you simply 'import Data.SBV', then
    you will get the default SMT solver, which is currently Z3. The value
    'defaultSMTSolver' refers to z3 (currently), and 'sbvCurrentSolver' refers
    to the chosen solver as determined by the imported module. (The latter is
    useful for modifying options to the SMT solver in an solver-agnostic way.)
  - Various improvements to Z3 model parsing routines.
  - New web page for SBV: http://leventerkok.github.com/sbv/ is now online.

### Version 2.8, 2012-11-29

  - Rename the SNum class to SIntegral, and make it index over regular
    types. This makes it much more useful, simplifying coding of
    polymorphic symbolic functions over integral types, which is
    the common case.
  - Add the functions:
  	- sbvShiftLeft
	- sbvShiftRight
    which can accommodate unsigned symbolic shift amounts. Note that
    one cannot use the Haskell shiftL/shiftR functions from the Bits class since
    they are hard-wired to take 'Int' values as the shift amounts only.
  - Add a new function 'sbvArithShiftRight', which is the same as
    a shift-right, except it uses the MSB of the input as the bit to fill
    in (instead of always filling in with 0 bits). Note that this is
    the same as shiftRight for signed values, but differs from a shiftRight
    when the input is unsigned. (There is no Haskell analogue of this
    function, as Haskell shiftR is always arithmetic for signed
    types and logical for unsigned ones.) This variant is designed for
    use cases when one uses the underlying unsigned SMT-Lib representation
    to implement custom signed operations, for instance.
  - Several typo fixes.

### Version 2.7, 2012-10-21

  - Add missing QuickCheck instance for SReal
  - When dealing with concrete SReals, make sure to operate
    only on exact algebraic reals on the Haskell side, leaving
    true algebraic reals (i.e., those that are roots of polynomials
    that cannot be expressed as a rational) symbolic. This avoids
    issues with functions that we cannot implement directly on
    the Haskell side, like exact square-roots.
  - Documentation tweaks, typo fixes etc.
  - Rename BVDivisible class to SDivisible; since SInteger
    is also an instance of this class, and SDivisible is a
    more appropriate name to start with. Also add sQuot and sRem
    methods; along with sDivMod, sDiv, and sMod, with usual
    semantics. 
  - Improve test suite, adding many constant-folding tests
    and start using cabal based tests (--enable-tests option.)

### Versions 2.4, 2.5, and 2.6: Around mid October 2012

  - Workaround issues related hackage compilation, in particular to the
    problem with the new containers package release, which does provide
    an NFData instance for sequences.
  - Add explicit Num requirements when necessary, as the Bits class
    no longer does this.
  - Remove dependency on the hackage package strict-concurrency, as
    hackage can no longer compile it due to some dependency mismatch.
  - Add forgotten Real class instance for the type 'AlgReal'
  - Stop putting bounds on hackage dependencies, as they cause
    more trouble then they actually help. (See the discussion
    here: http://www.haskell.org/pipermail/haskell-cafe/2012-July/102352.html.)

### Version 2.3, 2012-07-20

  - Maintanence release, no new features.
  - Tweak cabal dependencies to avoid using packages that are newer
    than those that come with ghc-7.4.2. Apparently this is a no-no
    that breaks many things, see the discussion in this thread:
      http://www.haskell.org/pipermail/haskell-cafe/2012-July/102352.html
    In particular, the use of containers >= 0.5 is *not* OK until we have
    a version of GHC that comes with that version.

### Version 2.2, 2012-07-17

  - Maintanence release, no new features.
  - Update cabal dependencies, in particular fix the
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
    detalied below:
      http://stackoverflow.com/questions/9426420/soundness-issue-with-integer-bv-mixed-benchmarks
    As a consequence, mixed Integer/BV problems can cause soundness issues in Z3
    and does in SBV. Unfortunately, it is too severe for SBV to add the woraround
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
    for sat/allSat. (Previously we were allways using forAll_, which is
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
     via constrain are satisfable. This is useful to prevent vacuous passes,
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
    
  - Reimplement sharing using Stable names, inspired
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
  * Specification bug in Legatos multipler example

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
