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

- `sbv-tutorial.pdf`: rendered manuscript.
- `sbv-tutorial.tex`: manuscript in ACM `acmsmall` format (`review,anonymous,nonacm`).
- `references.bib`: bibliography.
- `EDITORIAL.md`: submission notes, evidence map, and open items for the author.
- `examples/TutorialExamples.hs`: executable companion; source of the listings.
- `examples/adder-check.c`: independent exhaustive oracle for generated C.
- `results/validation.txt`: execution record, source revision, input hashes, and tool versions.

## Build the PDF

From this directory, with Tectonic installed:

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
declarations quoted verbatim from `Documentation/SBV/Examples/TP/TautologyChecker.hs`.
It fails if the manuscript refers to a listing that has no source. Edit the
Haskell sources, never the generated snippets. Short `ghci` transcripts and the
abbreviated `normalize` and internal-representation listings are typed directly
in the manuscript; the behavior they show is exercised by the companion.

## Reproduce the examples

The checked environment uses the SBV 14.10 source tree, GHC 9.14.1,
Cabal 3.16.1.0, Z3 5.3.2, and CVC5 1.4.2. This identifies a tested source
snapshot, not a claim that an arbitrary Hackage release has the same API.
The exact repository revision and source hashes are in `results/validation.txt`.

Build the library from the repository root, then run the companion:

```sh
cabal build --offline lib:sbv
python3 Artifacts/Tutorial/validate.py
```

Alternatively, after building SBV, run `make validate` from this directory. The
script requires `ghc`, `cabal`, `z3`, `cvc5`, and a C compiler named `cc`.
The Haskell package does not install the solver executables.

For interactive use, after building SBV, start from the repository root:

```sh
cabal exec --offline -- ghci -ignore-dot-ghci -i -package sbv \
  Artifacts/Tutorial/examples/TutorialExamples.hs
```

Then enable the extensions used in interactive expressions:

```haskell
:set -XOverloadedLists -XScopedTypeVariables
:set -XDataKinds -XTypeApplications
prove satAddSpec
runTP sumNonNeg
runTP (reverseLength @Word8)
bookKeepingAbstract
runTP kadaneCorrect
runTP mirrorCorrect
```

Validation compiles the companion with `-Wall -Werror` and exercises the paper's
examples, checking results independently where possible. Counterexamples are
re-checked with Haskell arithmetic, the production optimum is compared with all
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
and completeness proofs, and an exhaustive check of the generated C adder against
a C oracle built with `-O2`, warnings as errors, and undefined-behavior
sanitization. Each Haskell check has a 120-second outer timeout, which is a
validation failure. Two teaching examples intentionally use a five-second
solver timeout: the automatic sum attempt may return unknown, and the weak
reversal attempt demonstrates an unsuccessful proof. Neither outcome is counted
as a proof; the corresponding inductive proofs must succeed separately.
Running the script replaces `results/validation.txt`.
The complete SBV regression suite is outside this validation.

## Submission notes

The 2027 requirements still need checking when the call is available. The format
follows the [2026 call](https://icfp26.sigplan.org/home/haskellsymp-2026#Call-for-Papers-and-Talks):
acmsmall, lightweight double-blind, 25 pages for tutorials, labeled by subtitle.
The `nonacm` option suppresses placeholder publication metadata in this draft.
For the camera-ready version, remove `anonymous`, `review`, and `nonacm`, then
supply the publisher's actual metadata. `results/validation.txt` records local
paths and the git revision; anonymize it before uploading the companion as
supplementary material.
