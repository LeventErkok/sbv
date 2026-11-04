# From Counterexamples to Inductive Proofs: A Tutorial on SBV

A tutorial submission for the Haskell Symposium 2027. It takes a Haskell
programmer with no automated-reasoning background from one-line theorems to
inductive proofs: specifications, `sat`/`allSat`, a dedicated optimization section
covering measures, lexicographic/box/Pareto modes, real bounds with epsilon and
infinity, and solver limitations, programmable queries, symbolic datatypes,
arrays and symbolic memory, list induction, a detailed proof of Kadane's
algorithm, induction over expression trees, polymorphic and higher-order TP
proofs, closures, an overview of the verified tautology
checker, and C generation. The implementation discussion explains how TP
checks termination of the symbolic functions used in its proofs.
Proofs over symbolic lists and recursive ADTs concern finite, total values. The manuscript explains
this modeling choice, its limits for lazy Haskell programs, and its relation to
*Fast and Loose Reasoning is Morally Correct*.
The arrays section distinguishes total mappings over potentially infinite index
domains from the finite constructor structure of lists and recursive ADTs.
Two figures explain Kadane's invariant and how calculation hints become solver
queries. Troubleshooting covers solver startup, inconclusive results,
counterexamples, and stalled proof steps, with checked random-testing and
transcript-replay examples.

- `sbv-tutorial.pdf`: rendered manuscript.
- `sbv-tutorial.tex`: manuscript in ACM `acmsmall` format (`review,anonymous,nonacm`).
- `references.bib`: bibliography.
- `EDITORIAL.md`: submission notes, evidence map, and open items for the author.
- `sbv-tutorial.cabal`, `cabal.project`, `cabal.project.freeze`: standalone package,
  pinned SBV revision, dependency versions, and language extensions.
- `examples/TutorialExamples.hs`: executable companion; source of the listings.
- `examples/adder-check.c`: independent exhaustive oracle for generated C.
- `results/validation.txt`: execution record, source revision, input hashes, and tool versions.

## Build the PDF

First run `cabal build tutorial-examples` to fetch the pinned SBV sources used
for library listings. Then, from this directory with Tectonic installed:

```sh
make pdf
```

A particular binary can be selected with `make pdf TECTONIC=/path/to/tectonic`.
With a conventional TeX installation providing `acmart`, `listings`, `tikz`,
`tabularx`, and BibTeX:

```sh
python3 prepare.py
latexmk -pdf sbv-tutorial.tex
```

`prepare.py` extracts listings into `build/snippets/` from two places: blocks
between `-- BEGIN name` and `-- END name` in the companion, and a few
declarations quoted verbatim from `Documentation/SBV/Examples/TP/TautologyChecker.hs`
in Cabal's pinned source checkout. `companion.py` locates that checkout from the
build plan; neither extraction nor validation needs a surrounding SBV repository.
It fails if the manuscript refers to a listing that has no source, including
the breakable `\snippet*` form. `PAPER-ELIDE-BEGIN summary` and
`PAPER-ELIDE-END` comments replace a span only in the printed listing; the full
Haskell source is checked. The mirror proof uses this for its analogous `Mul`
case. Edit the Haskell sources, never the generated snippets. Short `ghci` transcripts and the
abbreviated `normalize` and internal-representation listings are typed directly
in the manuscript; the behavior they show is exercised by the companion.

## Reproduce the examples

Use GHC 9.14.1 and Cabal 3.16.1.0, with Git, Z3 5.3.2, and CVC5 1.4.2
on `PATH`. Full validation also needs Python 3 and a C compiler named `cc`.
Cabal does not install solver executables. The project pins SBV's 14.10 source
snapshot to published revision `ef9b2c0daeabb0e378eae9c584bb8bdbd815ddc3`;
`cabal.project.freeze` pins the dependency versions and Hackage index state.
This uses the development API rather than assuming a matching Hackage release.
The direct `base` dependency and freeze file target GHC 9.14.1 specifically.

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
```

Run the examples or the complete validation:

```sh
cabal run tutorial-examples
python3 validate.py
```

`make validate` runs the same script. After the initial build, validation uses
`cabal build --offline`, the Cabal-built executable, and the pinned SBV sources.
It records the companion's Git revision when available, the SBV revision and
source-package hash, and hashes of the validation inputs. It also works outside
a Git checkout, where input hashes identify the companion.

To create a source package that works outside this repository:

```sh
cabal sdist sbv-tutorial --output-directory build/package
```

Unpack the resulting archive and use the same commands from its directory.
The archive contains the project and freeze files, checked examples, validation
scripts, and paper sources. Cabal fetches SBV independently; it does not use the
author's checkout. This is the reproducible source package, not yet the final
anonymized submission supplement.

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

## Submission notes

The 2027 requirements still need checking when the call is available. The format
follows the [2026 call](https://icfp26.sigplan.org/home/haskellsymp-2026#Call-for-Papers-and-Talks):
acmsmall, lightweight double-blind, 25 pages for tutorials, labeled by subtitle.
That call does not explicitly exempt references; counting them is a working
assumption pending the 2027 call. No Haskell Symposium call was found on the
ICFP 2027 site or by search on 4 November 2026.
The `nonacm` option suppresses placeholder publication metadata in this draft.
For the camera-ready version, remove `anonymous`, `review`, and `nonacm`, then
supply the publisher's actual metadata. `results/validation.txt` records local
paths and the git revision; anonymize it before uploading the companion as
supplementary material.
