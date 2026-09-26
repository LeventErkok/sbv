# Editorial notes for the first draft

## Central argument

The manuscript argues that a Haskell verification library grows successfully
only when three boundaries stay explicit:

1. Haskell evaluation versus construction of symbolic computation.
2. A typed value versus the symbolic run and solver session to which it belongs.
3. The intended agreement between concrete evaluation, SMT translation, and C.

The historical material and examples are selected to support this argument.
The draft does not claim a new solver algorithm, measured usability benefits,
industrial adoption, or a formally verified implementation.

## Three placeholders reserved at the author's request

The PDF marks each of these visibly using `\authorplaceholder`:

1. **A consequential design choice** (representation section): alternatives,
   the actual reason for the decision, and what later experience revealed.
2. **A historical surprise** (incremental-solving section): a particular
   user request, solver behavior, or failed approach that changed the design.
3. **An application beyond the shipped examples** (evidence section): a
   concrete use, its outcome, difficulties, and evidence we may describe.

These should add the author's perspective, not repeat information already
available in the implementation. We can replace or move the boxes once the
episodes are chosen. No responses are needed until the author is ready.

## Evidence map

All source references below are relative to the repository root at the pinned
commit. The manuscript keeps most implementation filenames out of its prose;
this map makes the claims auditable during revision.

| Claim or episode | Evidence |
|---|---|
| Initial development in 2010; public release in 2011 | End of `CHANGES.md`, versions 0.0.0--0.9.7 |
| Early C generation and stable-name redesign | `CHANGES.md`, versions 0.9.12 and 0.9.14 |
| Interleaved execution replaces the earlier model | `CHANGES.md`, version 7.0; `Data/SBV/Control/Query.hs` |
| Transformer support | `CHANGES.md`, version 8.0; `Data/SBV/Trans.hs`; `Core/Symbolic.hs` |
| Expanded calculational/inductive interface | `CHANGES.md`, version 11.1 (then named KnuckleDragger) |
| User ADTs | `CHANGES.md`, version 13.0; `Data/SBV/Client.hs`; `Data/SBV/SCase.hs` |
| Typed wrapper and run-time kinds | `Data/SBV/Core/Data.hs`: `SBV`; `Core/Symbolic.hs`: `SVal`, `SV`, `State` |
| Two sharing mechanisms | `Core/Symbolic.hs`: `uncacheGen`, `newExpr` |
| Symbolic context checks | `Core/Symbolic.hs`: `checkConsistent`, `compatibleContext`, `runSymbolicInState` |
| Incremental synchronization | `Data/SBV/Control/Utils.hs`: `syncUpSolver`, `inNewContext`; `SMT/SMTLib2.hs`: `cvtInc` |
| Query-first function and rational registration | `CHANGES.md`, version 14.8; `SBVTestSuite/TestSuite/Basics/Recursive.hs` and query tests |
| Nested ADT registration matrix | `SBVTestSuite/TestSuite/ADT/Registration.hs` |
| Construction can diverge while unfolding recursion | `Documentation/SBV/Examples/CodeGeneration/Fibonacci.hs`: `fib0`, `fib1` |
| Accumulator reversal proof | `Documentation/SBV/Examples/TP/RevAcc.hs`; adapted and rerun in `paper/examples/PaperExamples.hs` |
| Constant folding and substitution | `Documentation/SBV/Examples/TP/ConstFold.hs`; expression/interpreter definitions in `TP/VM.hs` |
| Proof-step treatment of solver outcomes | `Data/SBV/TP/Kernel.hs`: `smtProofStep`; discussion excludes the internal formatting dry run |
| Termination dependencies | `Data/SBV/TP/Kernel.hs`: `lemmaWith`, `checkNewMeasures`; `Core/Model.hs`: function-definition checks |
| C lowering with conditional setup | `Data/SBV/Compilers/C/Lowering.hs`; `C/Backend.hs` |
| C runtime and numeric boundaries | `Data/SBV/Tools/CodeGen.hs`; `Data/SBV/Compilers/C.hs`; `CHANGES.md`, version 14.8 |
| Executed C boundary regressions | `SBVTestSuite/TestSuite/CodeGeneration/ScalarSafety.hs` and `PseudoBoolean.hs` |
| Concrete/solver paired tests | `SBVTestSuite/Utils/SBVTestFramework.hs`: `qc1`, `qc2` |
| Compile-time diagnostics | `SBVTestSuite/TestSuite/CompileTests/{SCase,PCase}` |

## What has actually been checked

The companion was compiled with `-Wall -Werror`. Seven small Haskell tasks,
the existing constant-folding development using CVC5, and exhaustive checking
of the generated C adder all passed. The complete log is in
`results/validation.txt`; do not generalize these results to the full suite.

The bibliography uses primary publications, author-hosted papers, and project
sources. Related-work prose deliberately avoids performance rankings. The
core comparison set is QuickCheck, observable sharing, Smten, Rosette,
Grisette, and Liquid Haskell's refinement reflection. SMT-LIB and Z3 are cited
as infrastructure. Further reading may suggest adding Cryptol/SAW, Lava,
hs-to-coq, or more direct comparisons for TP; no priority claim depends on
excluding them.

## Revision priorities after the first read

1. Decide whether the three-boundary argument expresses what the author most
   wants to say. Adjust the scope before polishing individual sentences.
2. Fill the three experience placeholders. Concrete lessons from applications
   will be more persuasive than adding more feature descriptions.
3. Review the trust/termination account carefully. The draft neither claims
   general coinduction nor treats finite symbolic sequences as lazy Haskell
   lists. It also distinguishes proof orchestration from independent proof
   certificate checking.
4. Add appropriate credit and acknowledgments for contributors. In particular,
   the release history credits Brian Schroeder for transformer support. A final
   first-person account should not imply that all contributions were made by
   one person. Confirm author list and affiliation rather than inferring them.
5. Review whether the code-generation section should remain a full section.
   It provides a concrete third interpretation and boundary tests, but should
   not overwhelm the longitudinal argument simply because it is recent.
6. Decide the actual venue/year and adjust length, anonymization, metadata,
   references, and disclosure accordingly. The current document is a named
   author-review draft using the 2026 format as a baseline.

The current C backend's release notes explicitly say it was largely developed
with LLM assistance. That fact has not been turned into an unsubstantiated
evaluation of AI-assisted development. If it becomes part of the paper's
argument, it needs the author's account and evidence.
