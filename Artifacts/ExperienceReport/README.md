# From Counterexamples to Inductive Proofs: A Tutorial on SBV

A tutorial submission for the Haskell Symposium 2027. It takes a Haskell
programmer with no automated-reasoning background from one-line theorems to
inductive proofs: specifications, `sat`/`allSat`/`optimize`, programmable
queries, symbolic datatypes, TP proofs (including a detailed proof of Kadane's
algorithm and an overview of the verified tautology checker), and C generation.

- `sbv-tutorial.pdf`: rendered manuscript.
- `sbv-tutorial.tex`: manuscript in ACM `acmsmall` format (`review,anonymous`).
- `references.bib`: bibliography.
- `EDITORIAL.md`: submission notes, evidence map, and open items for the author.
- `examples/TutorialExamples.hs`: executable companion; source of the listings.
- `examples/adder-check.c`: independent exhaustive oracle for generated C.
- `results/validation.txt`: execution record, source revision, and tool versions.

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

Build the library from the repository root, then run the companion:

```sh
cabal build --offline lib:sbv
python3 Artifacts/ExperienceReport/validate.py
```

Alternatively, after building SBV, run `make validate` from this directory. The
script requires `ghc`, `cabal`, `z3`, `cvc5`, and a C compiler named `cc`.

Validation compiles the companion with `-Wall -Werror` and runs every example in
the paper, checking results independently where possible (counterexamples are
re-checked with Haskell arithmetic, the synthesized expression is re-evaluated
by a plain Haskell interpreter, and the deliberately weak reversal proof must
fail). It also runs the exercise solutions, the tautology checker's soundness
and completeness proofs, and an exhaustive check of the generated C adder against
a C oracle built with `-O2`, warnings as errors, and undefined-behavior
sanitization. Each Haskell check has a 120-second timeout; a timeout is a
failure, never a proof. Running the script replaces `results/validation.txt`.
The complete SBV regression suite is outside this validation.

## Submission notes

The 2027 call for papers had not been published when this draft was prepared;
the format follows the 2026 call (acmsmall, lightweight double-blind, 25 pages
for tutorials, labeled by subtitle). Remove `anonymous` and `review` for the
camera-ready version. `results/validation.txt` records local paths and the git
revision; anonymize it before uploading the companion as supplementary material.
