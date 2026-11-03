# Editorial notes

## Target and format

Haskell Symposium 2027, tutorial category. The 2026 call evaluates tutorials on
whether they explain an aspect of Haskell or its ecosystem in a generally useful
way; they need not report original research. Tutorials are limited to 25 pages
in single-column `acmsmall`, must be labeled as such in the subtitle, and are
reviewed lightweight double-blind. The current draft is 17 pages including
references. Re-check all of this against the 2027 call when it appears.

## Structure

| Section | Teaches | Companion listings |
|---|---|---|
| 1 Introduction | Audience, roadmap, setup | (inline transcript) |
| 2 First proofs | Symbolic types, dotted operators, `ite`, what `prove` does | (inline) |
| 3 Specifications | Independent specs; a refuted wrong guard | `saturating`, `wrongAdd` |
| 4 Finding values | `allSat`, `optimize` | `idempotent`, `production` |
| 5 Haskell vs symbolic structure | Host lists, `SList`, `smtFunction`, why `prove` stalls | `hostSum`, `sumL` |
| 6 Programming the solver | `query` descent loop, dependency synchronization | `descent` |
| 7 Symbolic datatypes | `mkSymbolic`, `sCase`, synthesis by `sat` | `expr` |
| 8 Proofs by induction | `induct`, calculations, hints, generalization | `sumNonNeg`, `revAcc`, `revWeak`, `revAccCorrect` |
| 9 Kadane (detailed) | Spec, implementation, finding the invariant, proof | `mss`, `kadane`, `kadaneCorrect` |
| 10 Tautology checker (overview) | Measures, strong induction, proof architecture | library quotes |
| 11 C generation | `compileToC`, validating the translation boundary | `codegen` |
| 12 Under the hood | Deferred nodes, sharing, run contexts, synchronization | (inline) |
| 13 Pitfalls and trust | Checklist and trusted base | — |
| 14 Related tools | QuickCheck, Rosette, Grisette, Smten, what4, Liquid Haskell, Dafny | — |

Three exercises (Sections 3, 6, 8) have checked solutions in the companion.

## Evidence for implementation claims

Paths are relative to the repository root.

| Claim | Source |
|---|---|
| Deferred values, kinds, `Cached` | `Data/SBV/Core/Data.hs`, `Data/SBV/Core/Symbolic.hs` |
| Two forms of sharing | `Data/SBV/Core/Symbolic.hs`: `uncacheGen`, `newExpr` |
| Run-context checks | `Data/SBV/Core/Symbolic.hs`: `checkConsistent`, `compatibleContext` |
| Query dependency synchronization | `Data/SBV/Control/Utils.hs`: `inNewContext`, `syncUpSolver` |
| Automatic termination measures | `Data/SBV/Core/Model.hs`: `smtFunction` documentation |
| `Proven` vs `Modulo` reporting | `Data/SBV/TP/Utils.hs`: `RootOfTrust` and `Show (Proof a)` |
| C backend rejects quantifiers/uninterpreted sorts | `Data/SBV/Compilers/C/Backend.hs` |
| Kadane proof | `Documentation/SBV/Examples/TP/Kadane.hs` (companion has a reformatted copy) |
| Tautology checker: 21 TP lemmas, measures, `sInduct` | `Documentation/SBV/Examples/TP/TautologyChecker.hs` |
| ~40 TP example modules | `Documentation/SBV/Examples/TP/` (41 files, including helpers) |

Timings quoted in the text (Kadane ~0.1s with Z3; soundness and completeness
1–2s each) are single runs on the author's machine, not benchmarks.

## Open items for the author

- Verify the bibliography entries added for the tutorial: `bentley` (CACM 27(9),
  DOI), `boyermoore`, `imandraTautology` (author, year, and title are
  descriptive), `what4`, `liquidhaskell`, `dafny`, and the SMT-LIB 2.7 citation.
- Decide whether the tutorial should mention Cryptol/SAW or other users of SBV.
  The text currently makes no adoption claims.
- Consider whether Section 12 (Under the hood) earns its space in a tutorial or
  should shrink further in favor of more exercises.
- Confirm acknowledgments and any AI-assistance disclosure required by the venue.
  The initial draft and this revision were prepared with AI assistance at the
  author's request.
