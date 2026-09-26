# Verification as a Library: Lessons from Sixteen Years of SBV

An author-review draft of a Haskell Symposium experience report. The technical
account is based on SBV 14.8, commit
`f4f7a7a08445e63c2fb74c6f2084dfea5ad8b7d2`. It is a complete first draft with
three visible placeholders for the author's experiences. The initial PDF is
12 pages including references; it is not a submission-ready manuscript.

- `sbv-experience.pdf`: rendered paper, when built.
- `sbv-experience.tex`: manuscript in ACM `acmsmall` format.
- `references.bib`: bibliography with primary-source links.
- `EDITORIAL.md`: author questions, evidence map, and revision priorities.
- `examples/PaperExamples.hs`: executable Haskell listings and checks.
- `examples/adder-check.c`: independent exhaustive oracle for generated C.
- `results/validation.txt`: dated execution record, including tool versions.

## Build the PDF

With [Tectonic](https://tectonic-typesetting.github.io/) installed:

```sh
cd paper
make pdf
```

Tectonic obtains the ACM class, fonts, and other TeX dependencies on its first
run. The initial draft was rendered using Tectonic 0.17.0. You can choose an
existing binary with `make pdf TECTONIC=/path/to/tectonic`.

An ordinary TeX installation with `acmart`, `listings`, `tabularx`, and BibTeX
also works:

```sh
cd paper
python3 prepare.py
latexmk -pdf sbv-experience.tex
```

`prepare.py` extracts the listings from the executable source into
`build/snippets/`. Edit the Haskell source, not those generated fragments.

The named-author `nonacm` draft deliberately omits invented affiliation,
publication, DOI, and proceedings metadata. Before submission, choose the
actual venue and year, check its requirements, and prepare the appropriate
anonymous review version. The
[2026 call](https://icfp26.sigplan.org/home/haskellsymp-2026) supplies the current
planning baseline: single-column `acmsmall` and a 12-page experience-report
limit. It is not an intended submission to an already closed call.

## Reproduce the examples

The library and its examples must first be built and available to Cabal:

```sh
cabal build --offline lib:sbv
python3 paper/validate.py
```

Omit `--offline` from the build if dependencies are not already installed.
The validation script runs from any working directory. It compiles its
Haskell companion against the Cabal-selected SBV package, executes the seven
small checks and the existing constant-folding proof, generates a C adder,
and checks all 65,536 byte-input pairs with an independent wider-arithmetic
oracle. It requires `ghc`, `cabal`, `z3`, `cvc5`, and a C compiler named `cc`
supporting the flags shown in the log. The C check enables optimization,
warnings as errors, and undefined-behavior sanitization.

The recorded run used GHC 9.14.1, Cabal 3.16.1.0, Z3 5.1.0, CVC5 1.4.0,
and Apple Clang 21.0.0 on ARM64 macOS. Each Haskell check has a 120-second
timeout. The outer script also bounds subprocess execution. A timeout is
reported as an incomplete validation, never as a proof result.

The script replaces `results/validation.txt` with the new run. The elapsed
times in that log are diagnostic single-run timings, not a performance
evaluation. The full SBV test suite was not run for this draft.

## Draft preparation

The initial manuscript, companion, and editorial notes were prepared with
AI assistance at the author's request. Historical motivations and external
application stories have intentionally been left for the author. This is a
working provenance record; final acknowledgments and any required disclosure
should be written for the chosen venue after author review.
