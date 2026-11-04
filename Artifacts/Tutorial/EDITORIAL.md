# Editorial notes

## Target and format

Haskell Symposium 2027, tutorial category. The [2026 call](https://icfp26.sigplan.org/home/haskellsymp-2026#Call-for-Papers-and-Talks) evaluates tutorials on
whether they explain an aspect of Haskell or its ecosystem in a generally useful
way; they need not report original research. Tutorials are limited to 25 pages
in single-column `acmsmall`, must be labeled as such in the subtitle, and are
reviewed lightweight double-blind. The revised draft is 26 pages
including references. Re-check all of this against the 2027 call when it appears.
Pass 1 reduced the draft from 27 pages while adding datatype induction. Review
this structure before adding teaching aids or using the proposed reserve cuts.
The `nonacm` class option suppresses dummy DOI, price, and publication metadata;
remove it and insert the assigned metadata for publication.

## Structure

| Section | Teaches | Companion listings |
|---|---|---|
| 1 Introduction | Audience, roadmap, tested versions, runnable setup | `extensions`, `imports` |
| 2 First proofs | Symbolic types, dotted operators, `ite`, quantification, vacuity | (inline transcripts) |
| 3 Specifications | Independent specs; a refuted wrong guard | `saturating`, `wrongAdd` |
| 4 Finding values | `allSat` | `idempotent` |
| 5 Optimization | Objective measures, lexicographic/box/Pareto modes, extension-field bounds, strict-bound and nonlinear limitations | `production`, `realBounds` |
| 6 Haskell vs symbolic structure | Host lists, `SList`, `smtFunction`, bounded automatic attempt | `hostSum`, `sumL`, `sumWithoutInduction` |
| 7 Programming the solver | `query` descent loop, dependency synchronization | `descent` |
| 8 Symbolic datatypes | `mkSymbolic`, `sCase`, synthesis by `sat` | `expr` |
| 9 Arrays and symbolic memory | Functional updates, extensional equality, aliasing, bounds, infinite index domains | `writesCommute` |
| 10 Proofs by induction | `induct`, proof types, calculations, hints, generalization | `sumNonNeg`, `revAcc`, `revWeak`, `revAccCorrect`, `reverseCorrect` |
| 11 Kadane (detailed) | Independent segment oracle, spec, implementation, finding the invariant, proof | `mss`, `segmentOracle`, `kadane`, `kadaneCorrect` |
| 12 Induction over datatypes | Size measure, smaller-child lemmas, both child hypotheses; analogous multiplication case abbreviated | `exprMirror`, `mirrorCorrect` |
| 13 Polymorphic and higher-order proofs | Monomorphic instances, bookkeeping law, uninterpreted operations, conditional algebraic laws, explicit closure environments | `reverseLength`, `listProofImports`, `bookKeeping`, `bookKeepingRun`, `closure` |
| 14 Tautology checker (overview) | Lexicographic measures, strong induction beyond children, proof architecture | library quotes |
| 15 C generation | `compileToC`, validating the translation boundary | `codegen` |
| 16 Under the hood | Deferred nodes, sharing, run contexts, synchronization, termination obligations, finite-data semantics | (inline) |
| 17 Pitfalls and trust | Checklist and trusted base | — |
| 18 Related tools | QuickCheck, Rosette, Grisette, Smten, what4, Liquid Haskell, Dafny | — |

Three exercises (Sections 3, 7, 10) have checked solutions in the companion.

## Evidence for implementation claims

Paths are relative to the repository root.

| Claim | Source |
|---|---|
| Optimization modes and Z3 support | `Data/SBV/Control/Utils.hs`: `startOptimizer`; `Data/SBV/Core/Model.hs`: `Metric`; `Data/SBV/Control/Query.hs`: optimization result collection; `Data/SBV/Provers/*.hs`: capability flags |
| Arrays, read/write semantics, bulk updates | `Data/SBV/Core/Data.hs`: `SArray`; `Data/SBV/Core/Model.hs`: `readArray`, `writeArray`, `lambdaArray`; `Documentation/SBV/Examples/Misc/LambdaArray.hs`; SMT-LIB `ArraysEx` |
| Deferred values, kinds, `Cached` | `Data/SBV/Core/Data.hs`, `Data/SBV/Core/Symbolic.hs` |
| Two forms of sharing | `Data/SBV/Core/Symbolic.hs`: `uncacheGen`, `newExpr` |
| Run-context checks | `Data/SBV/Core/Symbolic.hs`: `checkConsistent`, `compatibleContext` |
| Query dependency synchronization | `Data/SBV/Control/Utils.hs`: `inNewContext`, `syncUpSolver` |
| Automatic termination measures, call conditions, mutual recursion | `Data/SBV/Core/Model.hs`: `autoGuess`, `checkMeasure`, `checkMutualGroup` |
| TP termination checks and final audit | `Data/SBV/TP/Kernel.hs`: `checkNewMeasures`; `Data/SBV/TP/Utils.hs`: `runTPWith` |
| Explicitly bypassed termination is a proof dependency | `Data/SBV/TP/Utils.hs`: `noTermCheckProof`; `Data/SBV/TP/Kernel.hs`: `lemmaWith` |
| Bookkeeping law and fold-over-append lemma | `Documentation/SBV/Examples/TP/Lists.hs`: `bookKeeping`, `foldrOverAppend` |
| Specialization of higher-order arguments and explicit environments | `Data/SBV/Core/Model.hs`: `smtHOFunctionGen`, `Closure`; `Data/SBV/List.hs`: `SMap` instances |
| Finite-list scope and design tradeoff | `Data/SBV/List.hs`: sequence operations; `Artifacts/DesignExplorations/infinite-lists-and-coinduction.md` (internal design rationale) |
| `Proven` vs `Modulo` reporting | `Data/SBV/TP/Utils.hs`: `RootOfTrust` and `Show (Proof a)` |
| C backend rejects quantifiers/uninterpreted sorts | `Data/SBV/Compilers/C/Backend.hs` |
| Kadane proof | `Documentation/SBV/Examples/TP/Kadane.hs` (companion has a reformatted copy) |
| Tautology checker: 21 TP lemmas, measures, `sInduct` | `Documentation/SBV/Examples/TP/TautologyChecker.hs` |
| ~40 TP example modules | `Documentation/SBV/Examples/TP/` (41 files, including helpers) |

The revision removes informal solver-speed claims. Timings in the validation
log are single-run diagnostics, not benchmarks. The log now records source
hashes as well as the revision, and distinguishes the intentionally inconclusive
teaching examples from successful proofs.

## Revision rationale

- Place the arrays section after symbolic datatypes.
  Prove that distinct-address writes commute; remove the premise to obtain an
  aliasing counterexample, checked independently with association-list lookup.
  Explain functional updates, extensional equality, explicit bounds, and bulk
  initialization via `lambdaArray`. Distinguish infinite index domains from
  infinite recursive constructor structure in both this section and the later
  finite-data discussion.

- Promote optimization to its own section, retaining the checked production
  example and adding objective measures, the three combination modes, and a
  simple two-objective comparison. Explain the Z3-only backend and SMT-LIB
  extension boundary. Warn about nonlinear arithmetic while recognizing Z3
  5.3 polynomial real optimization support; do not claim blanket lack of support.
- Add a real optimization example with epsilon and infinity, checking structured
  `ExtendedCV` results in the companion. Clarify that infinite bounds apply to
  integers as well as reals; infinitesimal bounds are specific to reals.
  Cite Z3 issue #5314 next to the example:
  strict inequalities are not reliably handled in general, and the observed
  output is tied to the tested version. The issue is about strict bounds (`<`,
  `>`), not the disequality operator (`/=`). Feasibility and solver success are
  insufficient evidence of optimality in this situation.

- Keep the path from small counterexamples to accumulator generalization and
  Kadane's invariant. Add the missing setup and a checked specialization of the
  reversal lemma so readers can reproduce the argument themselves.
- Clarify that a `Proof` type records quantifier shape, while the predicate lives
  in the proof value. Executing TP checks proof obligations; GHC typechecking
  alone does not prove them.
- Correct the descent-loop termination argument: bounded, strictly decreasing
  integers are essential. Having a minimum alone does not suffice over reals.
- Separate termination of recursive definitions, functional correctness, and
  algorithmic cost. Explain the tautology normalizer's lexicographic measure
  algebraically rather than referring only to unnamed complexity measures.
- Keep the user-facing termination obligations: inconsistent recursive equations,
  automatic decreasing measures, explicit measures, and visible `Modulo`
  dependencies for bypasses. Omit registration, caching, and audit internals.
- Prototype datatype induction before adding prose. `inductiveLemma` uses the
  generated datatype induction principle for `exprSizePos`; guided calculations
  use `sInduct` with `exprSize`, `exprSizePos`, and
  `exprSizeSmaller`, following the pattern in `Documentation/SBV/Examples/TP/Tree.hs`.
  Check all three constructor cases and explicitly instantiate both child
  hypotheses in each binary case, followed by a separate commutativity step.
  Print the addition case in full and elide the analogous multiplication case
  through explicit extraction markers. The section fits about one page.
  Starred snippets allow longer listings to break across pages; short listings
  and transcripts stay together. The manuscript remains 26 pages after this pass.
- Share `z3Timeout5` between the automatic sum attempt and weak reversal proof.
  Append its five-second per-call timeout to the default solver start options;
  the paper's reversal command uses the same checked configuration.
- Put Kadane directly after accumulator generalization, keep it a separate
  section, then introduce datatype induction. Group polymorphic scripts with
  higher-order proofs. Keep one full TP transcript and abbreviate the others.
- Distinguish Haskell type polymorphism from value quantification in a theorem.
  `reverseLength` is checked independently at `Integer` and `Word8`.
- Adapt the bookkeeping proof from `Documentation.SBV.Examples.TP.Lists`, with
  the helper `foldBase` proved in the companion and `foldrOverAppend` reused from
  the library. Check both an uninterpreted operation and an unconditional sum
  specialization; show a counterexample when the left-identity premise is lost.
- Give closures their own short subsection. The `shiftEach` example carries a
  symbolic offset explicitly; its length theorem quantifies over that offset
  and the input list.
- State the finite, total domain when introducing `SList`, list induction, and
  the nested-list bookkeeping law. Apply the same scope explicitly to recursive
  ADTs, including mutual and nested recursion, and distinguish unbounded size
  from infinite values in the expression-tree example. Add a forward reference
  from list induction to the later discussion of infinite lists.
  Condense the later explanation to one paragraph with the infinite-list
  reversal counterexample, the reason finite structure supports induction,
  the Fast and Loose citation, and the distinction from arrays' index domains.
  The fuller design rationale remains in the design exploration.
- Make the evidence for Kadane's specification independent of its recurrence:
  enumerate contiguous segments using ordinary Haskell, and compare on 3,906
  short lists plus three examples. Likewise independently check the production
  optimum by enumerating feasible plans.
- Scope the C claims to the generated byte adder and the tested executable.
  Exhaustive testing does not establish compiler correctness in general.

## Bibliography checks

Array laws and extensional equality were checked against the official SMT-LIB
`ArraysEx` theory, release of 21 July 2024 (SMT-LIB 2.7).

The optimization and arithmetic caveats were checked against the official Z3
Guide on 3 November 2026. The SMT-LIB 2.7 release of 9 September 2026 was also
checked for the optimization interface boundary; the manuscript retains its
existing versioned reference for the core language.

The CVC5 citation was added from the [publisher's record](https://link.springer.com/chapter/10.1007/978-3-030-99524-9_24).
The SMT-LIB citation now points to the specific 7 July 2025 revision rather
than a changing landing page. The [Imandra source](https://github.com/imandra-ai/imandrax-examples/blob/main/src/tautology.iml)
credits G. Passmore but states no publication date; the previous unverified 2025
date was replaced by “n.d.” and an access date. The title is explicitly descriptive.
The Boyer–Moore book, Liquid Haskell paper, Dafny paper, and what4 package were
checked against author, publisher, or package pages. Bentley's metadata is
retained; the ACM endpoint was inaccessible during this pass, so that item
remains for a final publisher-record check.
The *Fast and Loose* paper was read from the author's PDF, particularly
Sections 2, 7, 9, 10, and 13. Its author order follows that PDF and the
[Chalmers record](https://research.chalmers.se/publication/23040); pages and DOI
also agree with Oxford's publication listing. Its use here is conceptual:
the paper formalizes a particular language and does not establish a general
transfer theorem from SBV to Haskell.

## Open items for the author

- Verify `bentley` directly against the publisher's record (CACM 27(9),
  pages 865–873, DOI 10.1145/358234.381162).
- Package a stable supplementary artifact and supply its review-compatible
  location. The current companion assumes this repository layout; its log
  contains identifying local paths that should be removed for anonymous review.
- Decide whether the tutorial should mention Cryptol/SAW or other users of SBV.
  The text currently makes no adoption claims.
- Confirm acknowledgments and any AI-assistance disclosure required by the venue.
  The initial draft and this revision were prepared with AI assistance at the
  author's request.
