# Verification as a Library: Symbolic Programs and Compositional Proofs in SBV

A conference-style experience report about what SBV offers, how its interesting
mechanisms work, and what their composition contributes. The argument connects
typed symbolic expressions, programmable solver sessions, and structured proofs;
C generation supplies a second interpretation and a concrete validation boundary.

- `sbv-experience.pdf`: rendered manuscript.
- `sbv-experience.tex`: manuscript in ACM `acmsmall` format.
- `references.bib`: bibliography with primary-source links.
- `EDITORIAL.md`: technical evidence map and remaining author-review considerations.
- `examples/PaperExamples.hs`: executable listings and semantic checks.
- `examples/adder-check.c`: independent exhaustive oracle for generated C.
- `results/validation.txt`: execution record, source revision, and tool versions.

## Build the PDF

From this directory, with Tectonic installed:

```sh
make pdf
```

Tectonic downloads TeX dependencies as needed. A particular binary can be selected
with `make pdf TECTONIC=/path/to/tectonic`. With a conventional TeX installation
providing `acmart`, `listings`, `tabularx`, and BibTeX:

```sh
python3 prepare.py
latexmk -pdf sbv-experience.tex
```

The five main listings are extracted from the Haskell companion into
`build/snippets/`. Edit the Haskell source rather than those generated files.
The introductory calls and deliberately incorrect adder are short explanatory
listings whose behavior is also exercised by the companion.

## Reproduce the examples

Build the library from the repository root, then run the companion:

```sh
cabal build --offline lib:sbv
python3 Artifacts/ExperienceReport/validate.py
```

Alternatively, after building SBV, run `make validate` from this directory.
Omit `--offline` from the library build if dependencies are unavailable locally.
The script locates the repository independently of the invoking directory.
It requires `ghc`, `cabal`, `z3`, `cvc5`, and a C compiler named `cc`.

Validation compiles the Haskell companion with `-Wall -Werror`, executes eight
small checks and the existing constant-folding proof, generates a C adder, and
checks every one of its 65,536 input pairs against a wider-arithmetic oracle.
The negative adder check asks for a counterexample to an incorrect overflow
guard and validates the returned inputs independently. The C build enables
optimization, strict warnings, and undefined-behavior sanitization.

Each Haskell task has a 120-second timeout; the script also bounds subprocess
execution. A timeout is an incomplete check, never a proof result. Running the
script replaces `results/validation.txt`. The recorded November 2, 2026 run passed
all ten tasks. Timings are diagnostic single runs, not benchmarks, and the
complete SBV regression suite is outside this validation.

## Manuscript status

The manuscript has a capabilities-centered argument, explicit contributions,
source-backed mechanism descriptions, and checked examples. Release chronology
and author-placeholder boxes have been removed. Source and tool revisions are
recorded for reproducibility rather than used to organize the paper.

The named-author `nonacm` format omits proceedings metadata. Select the actual
venue before applying its page limit, anonymity requirements, author affiliations,
and publication metadata. The evidence supports the technical design account;
it does not establish comparative performance, measured usability, or external
adoption. Author review should confirm credit, emphasis, and final disclosure.

The initial draft and this revision were prepared with AI assistance at the
author's request. Personal motivations and application anecdotes have not been
invented. This is a working provenance record; final acknowledgments and any
required disclosure should follow the chosen venue's requirements.
