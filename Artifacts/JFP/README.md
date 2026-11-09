# From counterexamples to proofs

**A tutorial on solver-aided reasoning in Haskell with SBV.**

This is the Journal of Functional Programming version, developed independently
from the Haskell Symposium manuscript in `../Tutorial`. It was seeded from that
directory at repository revision `b8a667ce1`; the original manuscript and
companion remain unchanged. Source filenames and executable names are retained
so the checked listings and companion commands stay familiar. Build caches are
local to this directory.

The paper teaches a progression from choosing a semantic domain and writing an
independent specification to finding counterexamples, structuring calculations,
and discovering inductive invariants. Search, optimization, datatypes, and arrays
illustrate modeling decisions; append associativity, reversal, Kadane's algorithm, expression-tree
transformations, binary search over arrays, and higher-order laws develop proof
guidance. Binary search first appears as a midpoint overflow bug, then returns
as an example of induction on a decreasing interval. Failed TP obligations explain
input models, observed values, incorrect Boolean hints, and function interpretations. The tautology-checker
walkthrough covers evaluation, normalization, branching, and both correctness
theorems. Stateful verification and mechanizing Bird's maximum-segment-sum
derivation are open-ended suggested projects with starting hints and library
examples. A final example
follows a verified function through C generation. The research-context section
connects these decisions to testing, symbolic evaluation, equational reasoning,
refinement types, and invariant-based verification.

The six checked exercises, two teaching figures, finite-data scope, termination
checks, and standalone companion are retained from the original tutorial.

- `sbv-tutorial.pdf`: rendered manuscript.
- `sbv-tutorial.tex`: manuscript in the official JFP `jfp-epi` review format.
- `jfp_format.py`: fetches and checksums the official class v1.2; the generated
  `jfp-epi.cls` and its downloaded archive are build artifacts.
- `references.bib`: bibliography.
- `EDITORIAL.md` (repository only): submission notes, evidence map, and open items for the author.
- `sbv-tutorial.cabal`, `cabal.project`, `cabal.project.freeze`: standalone package,
  pinned SBV revision, dependency versions, and language extensions.
- `examples/TutorialExamples.hs`: executable companion, inductive proofs, and synthesis loop.
- `examples/ExpandedExamples.hs`: worked domain, query, contract, string/set, and proof-audit examples.
- `examples/adder-check.c`: independent exhaustive oracle for generated C.
- `results/validation.txt`: execution record, source revision, input hashes, and tool versions.

## Build the PDF

First run `cabal build tutorial-examples` to fetch the pinned SBV sources used
for library listings. Then, from this directory with Tectonic installed:

```sh
make pdf
```

A particular binary can be selected with `make pdf TECTONIC=/path/to/tectonic`.
The first PDF build downloads the official JFP class; subsequent builds verify
and reuse it. The archive URL and SHA-256 hashes are pinned in `jfp_format.py`.
With a conventional TeX installation providing the class's dependencies,
`listings`, `tikz`, `tabularx`, and BibTeX:

```sh
python3 jfp_format.py
python3 prepare.py
latexmk -pdf sbv-tutorial.tex
```

`prepare.py` extracts listings into `build/snippets/` from two places: blocks
between `-- BEGIN name` and `-- END name` in both companion modules, and a few
declarations extracted from `Documentation/SBV/Examples/TP/TautologyChecker.hs`
and `Documentation/SBV/Examples/TP/BinarySearch.hs` in Cabal's pinned source checkout. `companion.py` locates that checkout from the
build plan; neither extraction nor validation needs a surrounding SBV repository.
It fails if the manuscript refers to a listing that has no source, including
the breakable `\snippet*` form, and rejects duplicate snippet names across modules. `PAPER-ELIDE-BEGIN summary` and
`PAPER-ELIDE-END` comments replace a span only in the printed listing; the full
Haskell source is checked. The mirror proof uses this for its analogous `Mul`
case. Two long tautology-checker listings are reindented for the page; extraction
checks that all non-whitespace characters match the pinned library source.
Edit the Haskell sources, never the generated snippets. Short `ghci` transcripts and the
internal-representation listing are typed directly
in the manuscript; the behavior they show is exercised by the companion.

## Reproduce the examples

Use GHC 9.14.1 and Cabal 3.16.1.0, with Git, Z3 5.3.2, and CVC5 1.4.2
on `PATH`. Full validation also needs Python 3 and a C compiler named `cc`.
Cabal does not install solver executables. The project pins SBV's 14.10 source
snapshot to published revision `ef9b2c0daeabb0e378eae9c584bb8bdbd815ddc3`;
`cabal.project.freeze` pins the dependency versions and Hackage index state.
This uses the development API rather than assuming a matching Hackage release.
The freeze file targets the tested GHC 9.14.1 environment. The package's `base`
bounds follow SBV's supported range; removing the freeze file lets readers try
other compiler versions, which have not been validated here.
`companion.py` reads Cabal's internal `plan.json` format, tested with Cabal
3.16.1.0; other Cabal versions may require updating that helper.

From the companion directory:

```sh
cabal update
cabal build tutorial-examples
cabal repl tutorial-examples
```

Cabal enables the declared extensions in GHCi, so no `:set` commands are needed:

```haskell
prove satAddSpec
runTP sumNonNeg
runTP (reverseLength @Word8)
bookKeepingAbstract
runTP kadaneCorrect
runTP mirrorCorrect
binarySearchProof
```

Each of the six worked exercises names its solution in the paper, and validation
checks all six. The state-transition and Bird-derivation projects in Suggested
projects are open-ended; they give starting hints rather than companion solutions:

| Exercise | Companion solutions |
|---|---|
| Saturating subtraction | `satSub`, `satSubSpec` |
| Lexicographic objectives and their order | `productionLex`, `productionLexReversed` |
| Largest solution below 100 | `largestBelow100` |
| Array last-write-wins | `lastWriteWins` |
| Accumulator reversal length | `revAccLength` |
| Nonempty Kadane (challenge) | `mssNonEmpty`, `kadaneNonEmpty`, `kadaneNonEmptyCorrect`, `segmentNonEmptyOracle` |

The nonempty Kadane theorem requires nonempty input. The total functions return
0 on `[]`, outside that contract; all-negative nonempty inputs retain their
negative optimum. Validation compares both functions with independently
enumerated nonempty segments on all 3,905 lists of length one through five over
`[-2..2]`, plus three examples, and runs the inductive proof. The optimization
exercise's two priority orders are checked against all feasible integer plans.

The new material can be checked separately:

```sh
cabal run tutorial-examples -- --expanded
cabal run tutorial-examples -- --synthesis
cabal run tutorial-examples -- --tp-failures
cabal run tutorial-examples -- --tautology-concrete
cabal run tutorial-examples -- --tautology
```

The `--expanded` group checks byte-field packing, a power-of-two bit trick,
exact rational and algebraic arithmetic, floating-point rounding and a finite
associativity counterexample, weighted soft constraints, ripple/lookahead circuit
equivalence, scoped queries, unsat-core replay, contracts, optional operations,
regex validation, set invariants, quantifier order, an encoding bridge, and proof
dependencies. Byte examples have exhaustive 256-input concrete checks; the soft
optimum is compared with all feasible choices. The circuit proof fixes eight bits.

The `--synthesis` group reuses `Expr` in a bounded affine template. Its candidate
solver keeps samples incrementally, and a separate verifier searches for an
arbitrary integer counterexample. Validation checks a rejected candidate against
`evalC`, enumerates all 49 coefficient pairs independently, checks the returned
program on 201 concrete inputs, and reruns universal verification. The grammar
is finite but the verification input domain is not bounded. A solver's unknown
answer is an error, never acceptance of a candidate.

In GHCi, bring the new worked examples into scope with
`:module + ExpandedExamples`. That module explicitly exports the tutorial's
examples and validation entry point; `Main` imports only `expandedChecks`.

The failure checks intentionally catch TP exceptions. Full validation also requires
`Falsifiable` diagnostics and independently replays the displayed input, step,
hint, and function models; an exception or timeout alone does not pass. The
incorrect-hint example enables `printAsms` to expose its separate proof obligation.
The tautology checks compare 70 formulas with an independent truth-table evaluator, verify the
worked assignments, and run the library's soundness and completeness proofs.

Run the examples or the complete validation:

```sh
cabal run tutorial-examples
python3 validate.py
```

`make validate` runs the same script. After the initial build, validation uses
`cabal build --offline -fstrict tutorial-examples`, the Cabal-built executable,
and the pinned SBV sources. The package's `strict` flag adds `-Werror` to its
normal `-Wall` settings, so validation rejects compiler warnings. Ordinary
builds do not enable this flag by default. To match validation when running
examples directly, use `cabal run -fstrict tutorial-examples`.
It records the companion's Git revision and working-tree status when available,
the SBV revision and source-package hash, and hashes of the manuscript,
bibliography, build configuration, and executable validation inputs. It also works outside
a Git checkout, where input hashes identify the companion.

To create a source package that works outside this repository:

```sh
cabal sdist sbv-tutorial --output-directory build/package
```

Unpack the resulting archive and use the same commands from its directory.
The archive contains the project and freeze files, checked examples, validation
scripts, and paper sources. Cabal fetches SBV independently; it does not use the
author's checkout. This is the reproducible companion source package. The PDF itself is built
separately; its class is obtained by the checksummed `jfp_format.py` helper.

Validation compiles the companion with `-Wall -Werror` and exercises the paper's
examples, checking results independently where possible. Counterexamples are
re-checked with Haskell arithmetic; the printed `(223,124)` overflow example is
checked explicitly. The production optimum is compared with all
feasible plans, and the synthesized expression is re-evaluated by a plain Haskell
interpreter. Kadane's algorithm and its recursive specification are compared with
an oracle that enumerates contiguous segments on all 3,906 lists of length at most
five over `[-2..2]`, plus three larger or illustrative cases. The deliberately
weak reversal proof must fail specifically at step 2; unrelated exceptions do
not count as the expected result. The new proof checks cover reversal length at
both `Integer` and `Word8`, the bookkeeping law for an uninterpreted operation
and for integer addition, and list-length preservation with a symbolic closure
environment. A concrete counterexample demonstrates why the bookkeeping law's
left-identity premise matters. A deliberately non-decreasing recursive definition
must be rejected by the termination checker.
The expression-tree proof checks all three constructors, using a size measure
and both child hypotheses to prove that mirroring preserves evaluation. Its
nonnegativity and smaller-child lemmas are also proved during validation.
Array checks prove that writes to distinct addresses commute and independently
recheck an aliasing counterexample using ordinary Haskell association-list lookup.
The real-bound example checks the tested solver's `ExtendedCV` results for
epsilon and infinity. This is a version-specific regression check, not a claim
that Z3 reliably handles every strict-bound optimization problem; the manuscript
discusses issue #5314 beside the example.

Binary search connects two different claims. The midpoint example, adapted from
`BitPrecise.BrokenSearch`, uses checked `SInt32` arithmetic to expose overflow,
checks every reported violation with ordinary Haskell arithmetic, and separately
proves the repair agrees with a widened `SInt64` calculation. The printed
`low = high = 2^30` example is checked explicitly. Use
`cabal run tutorial-examples -- --midpoint` for these checks alone.

The later example reuses the pinned `TP.BinarySearch.bsearch` algorithm over
integer-indexed arrays. The companion proves a strengthened contract: a present
target produces `Just i` with `i` in the interval and the right value, while an
absent target produces `Nothing`. Two range-restriction lemmas support induction
on `max (hi - lo + 1) 0`. Validation runs that proof with CVC5 and checks ten
concrete cases against list membership and indexing, including negative indices,
duplicates, boundary matches, absent targets, a singleton, and an empty interval.
Use `cabal run tutorial-examples -- --binary-search` for these checks alone.
This is not a proof of the complete search with fixed-width indices; conversions
and index updates would require further obligations. The upstream SBV modules
are unchanged, and both source files are hashed in the validation record.

Validation also runs the exercise solutions, the tautology checker's soundness
and completeness proofs, random tests of saturating addition, and a verbose
proof whose SMT-LIB transcript is replayed with Z3. It exhaustively checks the
generated C adder against
a C oracle built with `-O2`, warnings as errors, and undefined-behavior
sanitization. Each Haskell check has a 120-second outer timeout, which is a
validation failure. Two teaching examples intentionally use a five-second
solver timeout: the automatic sum attempt may return unknown, and the weak
reversal attempt demonstrates an unsuccessful proof. Neither outcome is counted
as a proof; the corresponding inductive proofs must succeed separately.
Both use `z3Timeout5`, which appends the timeout to Z3's default start options.
Running the script replaces `results/validation.txt`.
The complete SBV regression suite is outside this validation.

## JFP submission notes

The current [JFP scope and categories](https://jfp.episciences.org/en/about)
include Tutorial Papers. This draft develops a reasoning method through a tool;
it does not claim a new verification algorithm or a measured educational result.
The suitability analysis and remaining author decisions are in `EDITORIAL.md`.

The [current author instructions](https://jfp.episciences.org/en/for-authors)
require the `jfp-epi` class and single-anonymous review. This draft uses explicit
`review` mode, includes the author name, and displays the approved acknowledgments.
The class has no tutorial-specific article-type option; the subtitle identifies
the paper as a tutorial, and the category must be selected during submission.
No publication volume, DOI, or acceptance date has been invented. Supply the
author's preferred affiliation before submission.

Submission requires depositing the manuscript on arXiv, HAL, or Zenodo and then
submitting its identifier through Episciences. Nothing has been uploaded or
submitted. For arXiv, build a separate copy with `review=false` (no line numbers)
and provide JFP with the review copy as its instructions describe. The guide
states no fixed tutorial page limit; page count must still be checked after
formatting changes rather than carried over from the conference version.
Rechecked on 2026-11-09: the [scope page](https://manager.episciences.org/jfp/page/about)
describes 20–50 pages as common for regular papers, with shorter and longer papers
allowed; it gives no numerical tutorial limit. The current draft's 58 pages
therefore warrant an editorial length review, rather than a cut to a stated cap.

Keep the pinned SBV source snapshot until the matching Hackage release has been
validated. Migration requires updating `cabal.project`, source lookup, the freeze
file, and the manuscript's source-snapshot wording together. Git and author
identities are not anonymity problems for this venue. The companion license now
names Levent Erkok. AI-disclosure work remains deferred at the author's request;
the Preparation paragraph was removed at the author's request. Checking the
applicable disclosure policy and resolving any required statement remain open
submission tasks.
