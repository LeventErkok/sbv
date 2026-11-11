# JFP editorial notes

## Target and independence

Journal of Functional Programming, Tutorial Papers category. This directory was
seeded from `Artifacts/Tutorial` at revision `b8a667ce1` on 5 November 2026.
All JFP changes stay here; the Haskell Symposium version is preserved unchanged.
The companion filenames and example identifiers are retained deliberately.

The [current scope](https://jfp.episciences.org/en/about) permits tutorials
without original scientific results and emphasizes an insightful, coherent
presentation at graduate level. The [author instructions](https://jfp.episciences.org/en/for-authors)
require `jfp-epi` and single-anonymous review. Use the official v1.2 class with
explicit `review` mode, sentence-case headings, the author identity, and visible
acknowledgments. The class does not define a tutorial article-type option;
identify the category in the subtitle and submission form. Its publication
metadata remains unset for this draft. No fixed tutorial page limit is stated;
the former 25-page conference limit is not a JFP requirement.

The official class is fetched without modification by `jfp_format.py`, which
pins both its archive and class hashes. It is generated locally and excluded
from the source package; recipients obtain it through the same helper. The
package's original notices are preserved. Do not substitute the old CUP class.

## JFP adaptation and teaching argument

The organizing subject is solver-aided reasoning in a functional language.
SBV is the executable setting, and the contribution is the exposition rather
than a claim that the underlying proof techniques are new. Three decisions
structure the introduction: formulate a logical question, choose a representation,
and supply proof structure. The existing progression and checked examples remain.

- Frame search and optimization in terms of witnesses, objectives, and bounds.
- Introduce datatypes as both search spaces and domains of quantification;
  contrast constructor-based induction with observational equality of arrays.
- Explain the move from automatic queries to calculations as a division of work
  between the programmer's argument and the solver's local checks.
- Keep reversal and Kadane adjacent to expose generalization as a reusable step.
- Present C generation as a concrete translation boundary, returning to the
  original independent specification.
- Expand the research context around representation, proof guidance, and the
  meaning of a successful check. Avoid an unsupported ranking of tools.

Two published JFP tutorials guide this positioning: Danvy's 2022 fold–unfold
paper develops an explicit equational technique in Coq, including local functions
and proof tactics; Hutton's 2023 semantics tutorial develops a sequence of
concepts through one small expression language. Both belong to Cambridge's
[explicit Tutorial Papers collection](https://www.cambridge.org/core/journals/journal-of-functional-programming/article-type-collections/tutorial-papers).
They support this scope but do not imply editorial acceptance. An optional
pre-submission scope inquiry remains an author decision; none has been sent.

## Structure

| Section | Teaches | Companion listings |
|---|---|---|
| 1 Introduction | Audience, roadmap, pinned standalone package, runnable setup | Cabal commands |
| 2 First proofs | Symbolic types, dotted operators, `ite`, quantification, vacuity | (inline transcripts) |
| 3 Specifications | Independent specs; a refuted wrong guard; midpoint overflow, repair, and wider-arithmetic specification | `saturating`, `wrongAdd`, `midpoint`, `midpointSafety`, `midpointSpec` |
| 4 Finding values | `allSat` | `idempotent` |
| 5 Optimization | Objective measures, lexicographic/box/Pareto modes, extension-field bounds, strict-bound and nonlinear limitations | `production`, `realBounds` |
| 6 Haskell vs symbolic structure | Host lists, `SList`, `smtFunction`, bounded automatic attempt | `hostSum`, `sumL`, `sumWithoutInduction` |
| 7 Programming the solver | `query` descent loop, dependency synchronization | `descent` |
| 8 Symbolic datatypes | `mkSymbolic`, `sCase`, synthesis by `sat` | `expr` |
| 9 Arrays and symbolic memory | Functional updates, extensional equality, aliasing, bounds, infinite index domains | `writesCommute` |
| 10 Proofs by induction | `induct`, proof types, calculations, hints, generalization | `sumNonNeg`, `revAcc`, `revWeak`, `revAccCorrect`, `reverseCorrect` |
| 11 Kadane (detailed) | Independent segment oracle, spec, implementation, three-case invariant figure, proof | `mss`, `segmentOracle`, `kadane`, `kadaneCorrect` |
| 12 Induction on decreasing measures | Expression-tree size and child hypotheses; binary-search interval, range lemmas, explicit result contract | `exprMirror`, `mirrorCorrect`, `binarySearch` (library), `binarySearchContract` |
| 13 Polymorphic and higher-order proofs | Monomorphic instances, bookkeeping law, uninterpreted operations, conditional algebraic laws, explicit closure environments | `reverseLength`, `listProofImports`, `bookKeeping`, `bookKeepingRun`, `closure` |
| 14 Tautology checker (overview) | Lexicographic measures, strong induction beyond children, proof architecture | library quotes |
| 15 C generation | `compileToC`, validating the translation boundary | `codegen` |
| 16 Under the hood | Deferred nodes, sharing, run contexts, synchronization, termination obligations, finite-data semantics | (inline) |
| 17 Pitfalls and trust | Troubleshooting by outcome, diagnostics and replay, random testing, trusted base | `inspectSatAdd`; companion `testSatAdd` |
| 18 Connections to program reasoning | Testing, symbolic evaluation, equational reasoning, refinements, invariants, and proof scope | — |
| 19 Conclusion | Reusable method and further verified examples | — |

Six exercises (Sections 3, 5, 7, 9, 10, 11) name checked companion solutions.

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

## Inherited tutorial revision rationale (historical)

The notes below describe the conference version before the directory split.
Their page counts and anonymity decisions do not apply to the JFP version.
The executable examples and semantic boundaries they document are retained.

- The final prose pass leads the abstract with what readers learn and shortens
  its topic list. The conclusion recaps the method and names `ConstFold`,
  `InsertionSort`, and `VM` as next examples. Exercise solutions consistently
  run inline. The introduction discloses Codex's assistance with prose, figures,
  companion code and proofs, packaging, and validation; the disclosure remains
  visible in anonymous review mode. Removing the general further-reading
  paragraph avoids duplicating the conclusion's specific pointers. The rebuilt
  paper remains 25 pages including references; the final TeX pass has no
  overfull boxes or undefined references, and the last page was checked visually.
- Pass 3 adds lexicographic optimization with reversed priorities, array
  last-write-wins, and a nonempty Kadane challenge. The latter has an explicit
  nonempty-input precondition, a proved accumulator invariant, and an independent
  segment oracle covering 3,905 short lists plus three examples. Both objective
  orders are checked against finite enumeration. Every exercise names its
  companion solution, including the three existing exercises.
- Give the companion its own BSD-3-Clause review license, naming "the authors",
  and anonymize the TeX author field included in the source archive. Restore
  Levent Erkok's name for camera-ready. This notice also covers the author's
  adaptations of their SBV examples; the fetched SBV dependency is unchanged.
- Use `base >=4.19.2 && <5`, matching SBV's lower bound, while retaining the
  tested compiler's exact versions in the freeze file. Note that source lookup
  reads Cabal's internal plan format and was tested with Cabal 3.16.1.0.
- Bring the standalone Cabal package forward before exercises. Pin SBV 14.10
  to the published source revision `ef9b2c0daeabb0e378eae9c584bb8bdbd815ddc3`,
  freeze dependencies, and declare the extensions needed both for compilation
  and the interactive examples. Validation and extraction locate Cabal's fetched
  sources, not the surrounding repository. The source archive includes the
  project/freeze files and validation tools. Keep final anonymization separate.
  Verify it by unpacking outside the repository, building and running full
  validation there, and rebuilding the PDF. The retained log is from that
  standalone run, so hashes identify the companion rather than a Git revision.
- Add an explicit check of the paper's `(223,124)` example: `wrongAdd` gives 91,
  while `satAdd` and the mathematical specification give 255.
- Pass 2 adds troubleshooting to the pitfalls section, distinguishing startup
  failure, unknown/timeout, counterexample, and a stalled TP step. The companion
  runs random tests of `satAddSpec` before proving it, and validates verbose
  diagnostics, transcript creation, and replay through Z3.
  Keep early testing and general diagnostics before the failure checklist;
  counterexample advice compares concrete implementation and specification
  results. Place the Kadane figure before the paragraph introducing the split
  and keep the invariant with its preconditions on the same page.
- Replace the architecture figure with two teaching figures: Kadane's three
  segment locations and the correspondence between calculation hints and solver
  queries. The latter replaces the formula and most of the old §10.2 explanation.
  Retain the four implementation paragraphs without the architecture diagram.
- Use reserve cuts in arrays, the tautology overview (omit the completeness
  listing while still validating its proof), closures, and related tools.
  Exercises follow in Pass 3.

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
  and transcripts stay together. This completed Pass 1 at 26 pages.
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

## Bibliography audit — 4 November 2026

All 21 bibliography entries were checked, along with all 23 citation commands in
`sbv-tutorial.tex`. Every key resolves, every entry is cited, and no duplicate keys
exist. All 12 DOIs identify the intended works in publisher-deposited Crossref
metadata. Author order, title, venue, year, and page/article information were
compared with that metadata and, where it omits details, the paper itself or an
official publisher/project record. The table below records the evidence for the
claims at each citation, not merely the existence of a similarly titled work.
No fabricated work, wrong DOI, or unsupported citation-to-claim pairing was found.

| Key | Metadata and claim evidence | Result |
|---|---|---|
| `sbv` | [Official repository](https://github.com/LeventErkok/sbv) and pinned `sbv.cabal`: author, library title, version 14.10; the pinned commit is dated 3 November 2026. | Valid source-snapshot reference, not a claim of a Hackage release. SBV behavior is additionally backed by the pinned source and companion checks. |
| `z3strictbounds` | [Issue 5314](https://github.com/Z3Prover/z3/issues/5314): Erkök's report, 29 May 2021, and Bjørner's response, 30 May. The actual example minimizes a positive real and reports 1; the reply discusses strict bounds and infinitesimals. | Valid. Both names are credited because the citation explicitly includes the discussion. The paper correctly describes a version-sensitive limitation, not a universal prohibition on disequality. |
| `z3optimization` | [Official guide](https://microsoft.github.io/z3guide/docs/optimization/arithmeticaloptimization/): optimization command extensions; infinity and infinitesimal bounds; polynomial real optimization since Z3 5.3 and its limitations. | Claims supported. Changed publication year to `n.d.` and recorded access on 4 November 2026: a copyright footer does not date the page's publication. The SBV-only-Z3 claim is separately checked against all backend capability flags. |
| `z3arithmetic` | [Official guide](https://microsoft.github.io/z3guide/docs/theories/Arithmetic/), nonlinear-arithmetic discussion: undecidability over integers and incomplete solver behavior. | Claims supported. Changed publication year to `n.d.` with the current access date. The text does not claim that polynomial real arithmetic is undecidable. |
| `quickcheck` | [Publisher metadata](https://api.crossref.org/works/10.1145/351240.351266), [authors' institutional record and abstract](https://research.chalmers.se/en/publication/237427): Claessen and Hughes, 2000, ICFP, pp. 268–279; properties as Haskell functions and random inputs. | Valid. Crossref shortens the title to QuickCheck; the institutional record confirms the subtitle. The institutional record also lists the separate SIGPLAN Notices DOI; our proceedings DOI is valid and retained. |
| `fastloose` | [Publisher metadata](https://api.crossref.org/works/10.1145/1111037.1111056), [author-hosted paper](https://www.cs.ox.ac.uk/jeremy.gibbons/publications/fast+loose.pdf): all four authors in order, POPL 2006, pp. 206–217; abstract and total/partial-language discussion. | Valid. The manuscript invokes the relationship between total and partial reasoning; it does not claim that this paper proves transfer of arbitrary SBV theorems to Haskell. |
| `sharing` | [Publisher metadata](https://api.crossref.org/works/10.1145/1596638.1596653), [author-hosted paper](https://ku-fpg.github.io/files/Gill-09-TypeSafeReification.pdf): Gill, Haskell 2009, pp. 117–128; stable names and graph reification. | Valid. SBV's actual use of `makeStableName` was also checked in `Data/SBV/Core/Symbolic.hs`. |
| `smtarrays` | [Official ArraysEx theory](https://smt-lib.org/theories-ArraysEx.shtml): Tinelli, version 2.7, update/release 21 July 2024; both read-after-write axioms and extensionality. | Valid. The descriptive bibliography title denotes the theory, not a separate research article. |
| `smtlib` | [Versioned standard PDF](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf), [official BibTeX](https://smt-lib.org/biblio/BarFT-RR-25.bib): Barrett, Fontaine, Tinelli; Iowa technical report, 2025. The PDF cover gives 7 July 2025 and the language includes `define-fun-rec`/`define-funs-rec`. | Valid. An explicitly dated prior release is cited, not mislabeled as the latest revision. |
| `z3` | [Publisher metadata](https://api.crossref.org/works/10.1007/978-3-540-78800-3_24), [Microsoft Research record and abstract](https://www.microsoft.com/en-us/research/publication/z3-an-efficient-smt-solver/): de Moura and Bjørner, TACAS 2008, pp. 337–340. | Valid solver reference. The tested executable version 5.3.2 comes from the validation log, not the 2008 paper. |
| `cvc5` | [Springer record](https://link.springer.com/chapter/10.1007/978-3-030-99524-9_24) and Crossref: all 16 authors in order; TACAS 2022, LNCS 13243, pp. 415–442, Springer Cham. | Valid solver reference. The tested executable version 1.4.2 comes from the validation log. |
| `smten` | [Publisher metadata](https://api.crossref.org/works/10.1007/978-3-642-39799-8_45), [author-hosted paper](https://people.csail.mit.edu/ruhler/smten-cav13.pdf), Section 2: Uhler and Dave, CAV 2013, pp. 678–683; Haskell-derived symbolic input language translated to SMT. | Valid metadata and related-tool description. |
| `grisette` | [Publisher metadata](https://api.crossref.org/works/10.1145/3571209), [author-hosted published paper](https://lsrcz.github.io/files/POPL23.pdf), first page: Lu and Bodík, PACMPL 7 (POPL), article 16, 33 pages, January 2023; Haskell and state merging. | Valid. The printed article identifier is confirmed by the PDF even though Crossref represents its extent as pp. 455–487. |
| `reflection` | [Publisher metadata](https://api.crossref.org/works/10.1145/3158141), [published PDF in an author's institutional repository](https://www.pure.ed.ac.uk/ws/portalfiles/portal/53404764/popl18_p1.pdf): all seven authors, PACMPL 2 (POPL), article 53, 31 pages; equational proofs in Liquid Haskell. | Valid. Retain 2018: the publisher's reference block says January 2018, despite the December 2017 online date in Crossref and the repository cover sheet. Replaced the preprint URL with the published version (31 article pages plus a repository cover). |
| `rosette` | [Publisher metadata](https://api.crossref.org/works/10.1145/2594291.2594340), [author-hosted paper](https://homes.cs.washington.edu/~bodik/ucb/Files/2014/rosette-pldi2014.pdf): Torlak and Bodík, PLDI 2014, pp. 530–541; introduction and implementation describe symbolic execution in Racket. | Valid. The accent in Bodík is retained, consistent with his other cited work; unaccented Bodik is a source spelling variant. |
| `bentley` | [ACM's metadata deposit](https://api.crossref.org/works/10.1145/358234.381162): Bentley, CACM 27(9), September 1984, pp. 865–873. [Copy of the original column](https://www.cs.rpi.edu/~moorthy/Courses/CSCI2300/p865-bentley.pdf), Algorithm 4 and its history: linear scan, empty segment allowed, attribution to Kadane. | Valid. Added an Algorithm 4 locator. The column really does carry the subtitle Algorithm Design Techniques; the shorter publisher-metadata title remains as requested. The mirrored copy is used for content, not to override the publisher's page range. |
| `boyermoore` | [Author-hosted book](https://www.cs.utexas.edu/~boyer/acl.pdf): title/copyright pages confirm Boyer and Moore, Academic Press, New York, 1979. Chapter 4 develops and proves a checker for propositional IF expressions, including normalization and soundness/completeness. | Valid. Added a Chapter 4 locator. |
| `imandraTautology` | [Official source file](https://github.com/imandra-ai/imandrax-examples/blob/main/src/tautology.iml): G. Passmore credit, explicit Boyer–Moore 1979 attribution, the same formula constructors, normalization measures and verified checker. [Imandra's team page](https://www.imandra.ai/about) identifies Grant Passmore. | Valid source-code citation. Keep `n.d.` and the explicitly descriptive title; no publication date is invented. Access date refreshed. |
| `what4` | [Versioned official package record](https://hackage.haskell.org/package/what4-1.8): author Galois Inc., exact package synopsis, release uploaded 1 September 2026; description explains typed symbolic values and SAT/SMT interfaces. | Valid claim. Made the citation version-specific (1.8), so its 2026 year has a release basis rather than merely an access-date basis. |
| `liquidhaskell` | [Publisher metadata](https://api.crossref.org/works/10.1145/2628136.2628161), [author-hosted paper](https://goto.ucsd.edu/~rjhala/papers/refinement_types_for_haskell.pdf): five authors, ICFP 2014, pp. 269–282; refinement checking of Haskell. | Corrected Simon Peyton-Jones's spelling to match the cited paper and publisher deposit. Other metadata and the cited claim are valid. |
| `dafny` | [Springer record](https://link.springer.com/chapter/10.1007/978-3-642-17511-4_20): Leino, LPAR 2010, LNCS 6355, pp. 348–370, Springer Berlin/Heidelberg; abstract describes a language/verifier using SMT. [Official tutorial](https://dafny.org/dafny/OnlineTutorial/guide.html) corroborates user-supplied loop invariants and automated checking. | Valid metadata and related-tool description. |

Access and scope: several ACM landing pages block automated access. Their
metadata was checked through the publisher's Crossref deposit, and substantive
claims through the available paper copies, institutional abstracts, or official
documentation listed above. This is a bibliography and citation-support audit,
not an independent re-proof of the cited research. No unresolved identity or
claim-support problem remains. Raw fetched metadata and extracted text from that audit remain in the original
Tutorial directory's `build/reference-audit/` cache (not distributed).
The corrected bibliography was rebuilt and inspected in the 25-page PDF, with
no final-pass overfull boxes or undefined references. All 11 executable input
hashes still match `results/validation.txt`; this audit changes citations and
editorial documentation. The companion source archive was regenerated.

## JFP bibliography additions — 5 November 2026

The inherited audit above covers the original 21 entries. The two additions were
checked against the publisher-hosted papers, including their title pages and
the passages used in the new research-context section:

| Key | Primary evidence | Claim supported |
|---|---|---|
| `danvyfoldunfold` | [Publisher paper](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/CE55ACA989A03E9073540DCCEBA4E89C/S0956796822000107a.pdf/div-class-title-fold-unfold-lemmas-for-reasoning-about-recursive-programs-using-the-coq-proof-assistant-div.pdf), §§2–4, 8–10; DOI 10.1017/S0956796822000107; Olivier Danvy, JFP 32, e13, 27 pages, 2022. | Constructor equations, controlled equational rewriting in Coq, and explicit understanding of recursive proofs. The relationship to SBV's mirror calculation is our comparison, not a claim made by Danvy. |
| `huttonsemantics` | [Publisher paper](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/EC2C046CF94382B3B408036B84475DC7/S0956796823000072a.pdf/programming_language_semantics_its_easy_as_123.pdf), §§1–3, 8–9; DOI 10.1017/S0956796823000072; Graham Hutton, JFP 33, e9, 26 pages, 2023. | A minimal arithmetic language supports semantic descriptions, induction, and derivation of an abstract machine. It does not claim to verify SBV or our evaluator. |

The expanded refinement-reflection discussion was checked against the
[published paper](https://www.pure.ed.ac.uk/ws/portalfiles/portal/53404764/popl18_p1.pdf),
abstract and §§1–2: definitions reflected into refinements, case splits and
induction expressed through Haskell programs. No claim is made that GHC alone
checks SBV theorems, or that the systems establish identical semantic claims.

## Initial JFP build and validation — 5 November 2026 (historical)

This records the first JFP adaptation, before the binary-search additions below.

- The official v1.2 review-class build produces **30 pages including references**.
  The larger count includes the change from ACM to JFP layout as well as the
  expanded conceptual introduction and research context; it is not a count in
  the former conference format.
- The final TeX pass has no overfull boxes or undefined citations/references.
  Title page, calculation and Kadane figures, research-context pages, and final
  references were rendered and inspected. Paragraph and table underfull-box
  notices and a monospace italic font substitution are non-fatal.
- All 23 bibliography entries are cited; there are no duplicate keys or labels
  and all section references resolve. The two added citations are documented
  above with primary evidence.
- `make validate` passes in this directory. `results/validation.txt` identifies
  the current repository base, the uncommitted JFP directory, tool versions,
  and hashes of both executable inputs and the manuscript/build inputs.
  The original Haskell and C example sources are unchanged.
- `cabal sdist sbv-tutorial --output-directory build/package` succeeds. The
  archive's sources were compared with this directory; the official class
  helper was run successfully from the unpacked archive, using the cached
  official ZIP, and its cached-class verification was checked. The full solver
  validation was run here, not repeated from that temporary unpacked archive.
- All 17 tracked files in `Artifacts/Tutorial` retain their pre-copy SHA-256
  hashes. The original PDF and validation record remain untouched.

## Binary search additions — 5 November 2026

Section 3.2 adapts `BitPrecise.BrokenSearch` to show the overflow in
`(low + high) / 2`, a checked-arithmetic repair, and a separate specification
computed after widening both inputs to `SInt64`. Validation rejects inconclusive
safety results, rechecks actual overflow models independently, proves the repair,
and checks the printed power-of-two counterexample.

Section 12 is now "Induction on decreasing measures": expression trees in 12.1,
then "Revisiting binary search" in 12.2. The latter quotes the actual `bsearch`
algorithm from the pinned library, states a result contract, and explains its
induction on interval length. It calls back to 3.2 and explicitly separates
unbounded-index algorithm correctness from fixed-width midpoint correctness.

The original library's positive-case theorem uses `fromJust` without explicit
`isJust` or returned-index bounds. The companion instead proves `searchContract`,
which includes those conditions. Its two range-restriction lemmas preserve both
sortedness and target membership in the selected half. The stronger theorem is
proved directly, without assuming the library's weaker theorem. No changes were
made to either upstream module. Ten additional model checks compare search
results with ordinary list membership and indexing.

The new `blochbinarysearch` reference was verified against the
[Google Research original](https://research.google/blog/extra-extra-read-all-about-it-nearly-all-binary-searches-and-mergesorts-are-broken/):
Joshua Bloch, 2 June 2006, "Extra, Extra - Read All About It: Nearly All Binary
Searches and Mergesorts are Broken." The article identifies overflow in the
midpoint sum and gives the subtraction-based repair. Our arithmetic oracle and
TP proof provide the evidence for our own claims; the blog is historical context.

The resulting PDF has **33 pages including references**, up from 30. The new
subsections are 3.2 and 12.2; the latter fits on roughly one page plus its opening
paragraph. The final build has no overfull boxes or unresolved references, and
the new pages were inspected visually. All 24 bibliography entries are cited.
`make validate` passes with matching current input hashes, including both pinned
binary-search source modules. HLint reports no hints. The source archive is
regenerated, and all 17 tracked files in the original Tutorial directory still
match their pre-copy hashes.

## Open items for the author

- Confirm the preferred affiliation for the JFP author block. The author name
  and contact email come from the SBV package; no affiliation is guessed.
- Decide whether to request an editorial scope assessment before submission.
  Tutorial Papers is the intended category; Tools and Applications is an
  alternative only if the editors recommend a different emphasis.
- Recheck the live JFP instructions at submission, deposit the chosen manuscript
  version, and supply the repository identifier through Episciences. The
  manuscript and companion have not been uploaded or submitted.
- Retain the validated SBV Git pin until the matching Hackage release is tested.
  Then remove the source-repository stanza, update source discovery and the
  freeze file, revise the source-snapshot wording, and rerun the checks. The
  GitHub URL does not need anonymization for JFP's single-anonymous review.
- After re-pinning to SBV with the new `Counterexample` output spelling,
  regenerate the validation log and remove the temporary spelling note in
  "Following along" and the spelling-update qualification before the
  `badLengthProof` diagnostic.
- AI-disclosure work remains deferred at the author's request. The inherited
  Preparation paragraph was removed at the author's request. Open submission
  task: check the applicable disclosure policy and resolve any required final
  wording. There is currently no disclosure statement in the manuscript.
- Supply actual publication metadata only after acceptance; keep the approved
  acknowledgments visible. Select the tutorial category in the submission form.


## November 2026: TP failures, tautology checker, and suggested project

The former state-transition chapter is now an open-ended exercise under
Suggested projects, after Connections. It supplies a concrete initial state,
transition, safety goal, staged tasks, and hints linked to the pinned
`ProofTools.BMC`, `ProofTools.Strengthen`, and `WeakestPreconditions.Basics`
modules. It is not counted among the six exercises with companion solutions.
The abstract and roadmap reflect this change of role.

A new TP-failure section distinguishes refuted theorems, refuted intermediate
steps in true theorems, and inconclusive results. Its wrong-length example is
adapted from `TP.Basics`; the uninterpreted-predicate example runs that module's
`forallDisjunctionNot` directly. Validation replays the actual printed models,
including `observe` values and the finite descriptions of the predicates.

The expanded tautology-checker section follows representation and evaluation,
normalization and its lexicographic measure, the complete checking traversal,
a worked implication example, generalized soundness, and constructive
completeness. Listings come from the pinned library. An independent Haskell
truth-table oracle checks 70 formulas, including nested conditions, and the
companion still runs both universal correctness theorems with their dependencies.
The Haskell Symposium copy remains unchanged; its companion and the JFP
companion intentionally diverge.

Verification snapshot, 2026-11-09, after append associativity, the incorrect
hint, and the Bird project: the snapshot includes the expanded tautology checker
and both suggested projects. Consult the current PDF and contents for section
numbers and pagination in later revisions.
The PDF has no overfull boxes
or unresolved references, and the affected pages were inspected. The full
companion validation passes, including replay of the actual TP diagnostic
models, truth-table checks, both universal tautology proofs, and generated C.
Two long library listings are reindented for readability; extraction verifies
that their non-whitespace content matches the pinned source. HLint reports no
hints, and validation builds with warnings treated as errors.

The incorrect-justification example adds `?? (n .>= 0)` to a valid calculation
of `n + n == 2*n`. The pinned TP engine proves Boolean hints separately before
using them; `printAsms = True` exposes the otherwise quiet failing check.
The diagnostic specifically says `assumptions for badJustification.1`, with a
negative input. Validation replays that input against both the false hint and
the true equality, distinguishing a bad justification from a bad step.

Append associativity now follows the first inductive example in section 15.2.
It makes the empty-list base case explicit in prose and shows two unfoldings,
instantiation of the tail hypothesis at the current `ys` and `zs`, and a final
folding step. The companion checks the universal theorem by list induction.

Citation added to the Kadane section after the segment-oracle paragraph:
Richard S. Bird, "Algebraic Identities for Program Calculation", The Computer
Journal 32(2), 122–126 (1989), DOI 10.1093/comjnl/32.2.122. Bibliographic details
were checked against Oxford's repository and Bird's publication list. The
publisher PDF could not be retrieved, but the actual derivation is reproduced
in Figure 9, page 14, of Jeremy Gibbons's "The School of Squiggol"
(https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/squiggol-history.pdf),
and that image was inspected. It uses map/fold promotion, Horner's rule, the
scan lemma, and fold-scan fusion to reach a paired left fold. Its pair is our
`(msf, meh)`. It is cited as the algebraic derivation of the same algorithm,
alongside Bentley's existing algorithm citation. The comparison explicitly
states that we have not mechanized Bird's derivation: the current proof checks
the accumulator implementation against a recursive specification. A faithful
TP rendition is expected to require more proof infrastructure, not claimed to
be impossible. The pinned `TP.Lists` includes `foldrMapFusion` and `foldrFusion`,
so the paragraph acknowledges existing higher-order support and links forward
to our bookkeeping proof. The original notation is Miranda-like, not literally
Haskell.

Section 25.2 now proposes mechanizing Bird's maximum-segment-sum derivation as
an advanced project. It starts from segment enumeration, proceeds through
Horner's rule and a scan, and ends with a paired left fold connected to Kadane.
Hints recommend pointwise statements, integer instances first, explicit lemma
instantiation, and the existing fold-fusion examples as templates. It explicitly
does not promise a companion solution or a proof as compact as Bird's paper.
The roadmap, setup wording, and README now account for both open-ended projects.

### 2026-11-09: pre-commit review checks

Compared the normalization measure with the pinned `TautologyChecker.hs`:
`ifDepth` is zero except for `If c _ _`, where it is `1 + ifDepth c`;
`ifComplexity` is one except for `If c l r`, where it is `C(c)*(C(l)+C(r))`.
For `If (If p q r) l r'`, the original complexity is
`C(p)*(C(q)+C(r))*(C(l)+C(r'))`. The rewritten complexity is
`C(p)*(C(q)*(C(l)+C(r')) + C(r)*(C(l)+C(r')))`, equal by distributivity.
Depth changes from `2+D(p)` to `1+D(p)`. Since every complexity is a positive
integer, `C(c)*(C(l)+C(r)) >= C(l)+C(r) > C(l)` and likewise for `r`.
The manuscript's claims therefore hold exactly. The source comment above
`normalize` saying the rewrite reduces complexity is imprecise; its definitions
and `normalizePreservesComplexity` lemma confirm preservation of the first
measure component. No change to the pinned library was made.

Both suggested-project headings now say "Project", matching their role outside
the six numbered exercises. The README documents validation's explicit `-fstrict`
flag and its `-Werror` effect. `expectTPFailure` still requires the pinned
exception format, but reports the actual exception if that format changes;
a successful action where rejection was expected also gets a specific diagnostic.
Disclosure-policy checking remains an open submission task; no disclosure was
added to the manuscript.

### 2026-11-09: filling the remaining outline

All twenty previously empty subsections now contain explanations and executable
examples. The original Symposium tutorial is unchanged. The material follows the
existing four-part structure; the state-transition and Bird projects remain
open-ended projects, not claimed implementations.

| Subsection | Teaching purpose and checked example |
|---|---|
| Signed and unsigned words | Fixed widths and interpretation; byte shifts and wraparound |
| Masks, shifts, rotations, and bit fields | Packing/extraction round trip, arithmetic oracle for every byte, rotation inverse |
| Widening, narrowing, and checked arithmetic | Range contract for an integer-to-byte round trip |
| Bit tricks and independent specifications | Power-of-two recognition against enumeration and population count |
| Rationals and algebraic reals | Exact thirds, rational construction, and an algebraic square-root model |
| Rounding modes and floating-point identities | Explicit rounding at 2^24 and finite nonassociativity |
| Soft constraints and weighted preferences | Violated-preference costs compared with all feasible choices |
| Circuit equivalence | Haskell builds an eight-bit ripple circuit, compared with lookahead and native addition |
| Scoped assumptions | Push/pop and temporary assumptions with independently expected results |
| Unsat cores | Named contradictory bounds; returned subset replayed in a fresh check |
| Uninterpreted functions and abstract sorts | Opaque keys and congruence, without assuming injectivity |
| Explicit assumptions and consistent contracts | Two-call progress, a concrete implementation witness, and contradiction detection |
| Partial operations | Optional list head and division, with constructor/value contracts |
| Regular expressions as specifications | Three-letter identifier validator proved equivalent to a regex |
| Sets and membership invariants | Activation preserves the allowed-set invariant |
| Quantifier order | One universal offset versus an input-dependent witness |
| Expression search from examples | Fixed affine Expr template, bounded coefficients, concrete evalC check |
| Counterexample-guided expression synthesis | Incremental candidate query plus a separate universal verifier |
| Encodings and solver selection | Byte/integer modular bridge, and the same field theorem with Z3 and CVC5 |
| Model validation and proof dependencies | A checked identity versus the same identity with sorry; trust-root/tree inspection |

`ExpandedExamples.hs` holds the domain and query examples. The synthesis helpers
remain with `Expr` in `TutorialExamples.hs`. The extractor now reads all companion
Haskell modules and rejects duplicate snippet names. Cabal declares the additional
module explicitly; validation includes its hash and both new executable groups.
The independent checks include all 256 bytes, all three preference choices, all
49 coefficient pairs, and ordinary Haskell evaluation of synthesized expressions.
The verifier searches unbounded integer inputs; finite testing does not replace it.
Unknown solver results never count as a successful synthesis result.

The circuit theorem is explicitly for eight bits. The expression grammar fixes
an affine tree shape, rather than promising unrestricted recursive-tree synthesis.
For strings, a generic recursive character predicate encountered a termination
measure limitation in this SBV snapshot; the tutorial instead uses a fixed
three-letter identifier and proves the complete equivalence. No pinned library
source was altered. Algebraic models are rechecked without conversion to Double.

New external sources were checked against the official SMT-LIB theory pages for
FixedSizeBitVectors, FloatingPoint, and UnicodeStrings. The CEGIS citation is
Solar-Lezama et al., "Combinatorial Sketching for Finite Programs", ASPLOS 2006,
pp. 404–415. The author-hosted PDF at
https://people.csail.mit.edu/asolar/papers/asplos06-final.pdf describes the
synthesize/verify loop; its printed author order is used. Seshia's bibliographic
page confirms venue, year, and pages, but lists the final two authors in the
opposite order, so the PDF takes precedence. No unverified DOI was added.

Completion checks for this earlier revision: the rebuilt main PDF had
57 pages before the mkSymbolic subsection was added; selected new pages were visually inspected. There are
no overfull boxes or unresolved references. Full `validate.py` passed, all 29
recorded input hashes match, HLint reports no hints in either companion module,
and `git diff --check` is clean. The refreshed Cabal source archive includes
`ExpandedExamples.hs`. Validation for this revision ran in the working checkout;
archive contents were inspected, but this run did not rebuild in a fresh unpacked
archive. The validation log identifies the parent commit and uncommitted draft
through its input hashes.

### 2026-11-09: review of the expanded sections

The unsat-core paragraph deliberately reports the observed checked run:
`["nonnegative","negative"]`. Its explanation that `upper` adds nothing refers
to that particular sufficient pair. Validation accepts any sufficient subset of
the known constraints, including non-minimal cores and different name orderings.
After changing solver versions or the example, inspect the reported core before
retaining the observed-output sentence; validation alone does not freeze it.

The floating-point paragraph now says explicitly that the companion refutes
`finiteAssociativity` at the fixed instance `(2^24,1,-2^24)`, rather than implying
that the solver searched freely for all three values. The example still refutes
the universal law. `ExpandedExamples` now exports its documented examples and
validation entry point explicitly, hiding the internal checking helpers. `Main`
imports only `expandedChecks`, avoiding incidental names from the example module;
the README explains how to bring the public examples into GHCi scope.

Length guidance rechecked on 2026-11-09 against the current Episciences pages:
https://jfp.episciences.org/for-authors and
https://manager.episciences.org/jfp/page/about . Neither sets a numerical tutorial
limit. The scope page describes regular papers as often 20–50 pages, explicitly
allowing shorter or longer papers. That range is not a tutorial cap. The tutorial
criteria instead emphasize gradual introduction, coherent presentation, and
careful writing. At this review, the draft had 57 pages including references,
before the mkSymbolic addition. An editorial length review remains necessary
before submission; absence of a numerical cap does not establish that the
manuscript's length will satisfy the editors.

### 2026-11-09: introducing mkSymbolic before its first use

Added "Generating symbolic types with mkSymbolic" as the first subsection of
Abstraction through contracts. It explains compile-time declaration generation,
Template Haskell type-name quotation, the top-level splice syntax, symbolic type
aliases and instances, and the constructor/tester/accessor interface. The existing
Key declaration is now its own extracted listing; the following opaque-function
example reuses it. The Expr section calls back instead of repeating the interface.

The induction paragraph is explicit: mkSymbolic generates the structural induction
schema consumed by inductiveLemma for enumerations and constructor datatypes;
constructor-free uninterpreted sorts receive none. Expr supplies a concrete
explanation of constructor obligations and hypotheses for both children, with a
forward link to exprSizePos and the guided mirror proof. This is distinct from
the calculational induct interface for integers and lists. No new algorithm or
unchecked example was introduced.

Checked against the pinned Data/SBV/Client.hs: mkSymbolicADT/mkADT generate the
alias, value instances, constructors, accessors, testers and case analyzer;
mkInductionSchema constructs HasInductionSchema instances, with ADTUninterpreted
explicitly excluded. TP/Kernel.hs confirms that inductiveLemmaWith supplies
inductionSchema to lemmaWith. Client.hs is now included in validation's input
hashes. The updated PDF is 58 pages at this snapshot; the new material occupies
roughly one page across pages 20–21. These pages were visually inspected, with
no overfull boxes or unresolved references.

### 2026-11-09: replacing the introductory opaque-type example

The initial mkSymbolic example was too small to demonstrate its main benefits.
The subsection now starts with the existing recursive Expr declaration, moving
that checked listing ahead of its evaluator rather than adding another datatype.
It follows generated constructors and guarded selectors with the existing
exprSize function and exprSizePos proof. The explanation makes the Num obligation
and the two recursive-child hypotheses explicit. Thus the generated induction
principle has a worked application at its introduction. Key is retained only as
the contrasting opaque-sort example in the next subsection.

The search section now starts from the already introduced Expr; the later mirror
proof reuses the introduced size and theorem. Listing markers changed, but the
Haskell definitions and proofs did not. This supersedes the earlier note about
using Key as the first example. The revised material spans pages 20–22 at this
snapshot; the complete PDF remains 58 pages. These pages were visually checked,
with no overfull boxes or unresolved references.

The earlier 57-page entries now explicitly describe their historical snapshots.
The current PDF's outline was inspected with PDFKit: the bookmark is exactly
"10.1 Generating symbolic types with mkSymbolic". The contents entry on page 2
was also visually checked; mkSymbolic renders correctly there. No title-macro
change was needed, and the current placement is retained. This check changed
only the editorial log, so the manuscript and validation inputs remain unchanged.

### 2026-11-09: positioning the host-language workflow

Added a short paragraph headed "Why not a proof assistant?" at the end of the introduction, immediately before
Following along and after the statement of the modeled-program scope. It presents
Lean, Isabelle, Agda, ACL2, and Rocq as valuable alternatives when a project can
invest in a formalization and maintain its correspondence with the Haskell code.
The tutorial's goal is to keep programs, specifications, and proofs in the host
language as far as possible, reducing the need to maintain definitions across
languages and reconcile their syntax and semantics. It explicitly retains SBV's
translation to solver logic; no claim about avoiding external solvers or proving
arbitrary Haskell source is made. No comparative capability or soundness claims
were added. The rebuilt PDF is 59 pages at this snapshot, and the introduction's
new paragraph was visually checked on page 5 without layout warnings.

### 2026-11-09: proof-assistant references and automation

The introduction's tool list is now explicitly illustrative ("among others"),
with citations for every named system. HOL4 and PVS were added as established
alternatives. The automation comparison is qualified: supported SMT obligations
can be discharged without explicit proof steps, while interactive development
typically asks for more guidance. Existing automation, including Sledgehammer's
SMT integration, and AI-assisted premise/tactic selection in LeanDojo prevent
this from becoming a blanket claim that proof assistants are manual. The final
sentence acknowledges that TP also needs guidance and returns to the purpose of
expressing that guidance in Haskell. This is discussion of proof automation,
not a manuscript-preparation disclosure; that separate item remains deferred.

New references checked against primary sources:

| Key | Verified source |
|---|---|
| lean4 | Official paper https://lean-lang.org/papers/lean4.pdf and publisher https://doi.org/10.1007/978-3-030-79876-5_37: de Moura and Ullrich, CADE 28, 2021, 625–635. |
| isabelle | Publisher https://doi.org/10.1007/3-540-45949-9: book, 2002, LNCS 2283. Author order Nipkow, Paulson, Wenzel follows the official tutorial title page at https://isabelle.in.tum.de/doc/tutorial.pdf; the publisher's catalogue labels/reorders them as editors. |
| agda | Chalmers record https://research.chalmers.se/publication/46311 and author-hosted thesis: Norell, 2007, Chalmers. |
| acl2 | Authors' book page https://www.cs.utexas.edu/~moore/publications/acl2-books/car/index.html: Kaufmann, Manolios, Moore; Kluwer, 2000. |
| rocq | Official versioned manual https://rocq-prover.org/doc/V9.2.0/refman/index.html, reached from the project's documentation page. No release year inferred; access date recorded. |
| hol4 | Publisher https://doi.org/10.1007/978-3-540-71067-7_6: Slind and Norrish, TPHOLs 2008, LNCS 5170, 28–32. |
| pvs | Authors' record https://www.csl.sri.com/papers/cade92-pvs/: Owre, Rushby, Shankar; CADE 1992, LNAI 607, 748–752. Removed the duplicate "and" in the site's BibTeX. |
| sledgehammer | Official manual https://isabelle.in.tum.de/doc/sledgehammer.pdf, dated 24 October 2026. Main author and contributors follow its title page; its introduction explicitly describes ATP/SMT integration. |
| leandojo | NeurIPS proceedings https://proceedings.nips.cc/paper_files/paper/2023/hash/4441469427094f8873d0fecb0c4e1cee-Abstract-Datasets_and_Benchmarks.html: title, nine authors, 2023, volume 36, DOI 10.52202/075280-0944. The authors' https://leandojo.org/leandojo.html explains premise retrieval and tactic generation. Cited as a published demonstration, not a claim of complete automation or a recommendation to install the deprecated original package. |

The revised introduction was visually checked on pages 5–6. At this snapshot
the complete PDF remains 59 pages, with no overfull boxes or undefined citations
or references. Bibliography style warnings concern omitted optional publication
fields; unsupported metadata was not invented to silence them.

### 2026-11-10: partial operations and exceptional inputs

Expanded the existing optional-results subsection, now titled "Partial operations
and exceptional inputs". A compact table distinguishes SBV's specified results
for ordinary integer/word, real, and rational zero division; IEEE floating-point
behavior; and unspecified values from invalid selectors. Earlier machine-word,
exact-arithmetic, and floating-point sections point forward to this explanation.
The text explicitly separates logical totality from host-language exceptions and
from proving that callers meet a precondition. Existing headOption/divOption
wrappers remain the examples of making failure an explicit result.

Source checks use the pinned SBV tree. Core/Model.hs documents and implements
sDiv/sQuot by zero as zero, with sMod/sRem returning the dividend; its Fractional
instance guards real zero division but leaves floating-point division to IEEE
semantics. Rational.hs gives SRational the same zero-result convention. In
contrast, sEDiv/sEMod are explicitly unconstrained at a zero divisor. Maybe.hs
implements fromJust as getJust_1 and documents the unspecified Nothing case.
List.hs documents empty-list head. The three newly referenced source files
Core/Model.hs, Maybe.hs, and List.hs are now included in the validation hashes
(Rational.hs and Client.hs were already included).

The new companion checks cover integer, unsigned-byte, signed-byte, real, and
rational zero division; Float/Double infinity and NaN examples; separate
satisfiable interpretations of fromJust Nothing; consistency of repeated uses
within one interpretation; empty-list head; and Euclidean zero division/modulus.
They also prove the isJust-guarded payload reconstruction law and both cases of
fromMaybe's explicit default. No arbitrary solver-selected value is frozen in
an expected transcript. The first focused run passed after resolving a shadowed
helper name; HLint is clean. The manuscript's exception-policy claims are about
the named symbolic APIs, not raw SMT-LIB operators or ordinary Haskell division.

The PDF was rebuilt and the subsection inspected on pages 24–26. At this snapshot
the paper has 60 pages including references, with no overfull boxes or unresolved
references. The historical page counts above describe earlier revisions.


### 2026-11-10: symbolic execution and assertion checking

Added "Symbolic execution and path conditions" at the start of the host-evaluation
section, with an introduction forward reference. It reuses the validated satAdd
example to connect symbolic inputs, branch guards, merged ite expressions, and
counterexample queries. The distinction between formula construction and SMT
solving leads into host recursion versus recursive logical definitions. It does
not describe SBV as an analyzer for arbitrary Haskell source or claim that merging
eliminates formula growth. Core/Model.hs supplies the ite/symbolicMerge evidence;
the execution-model section already explains shared expression graphs.

Citation provenance:
- King (1976), "Symbolic Execution and Program Testing", Communications of the ACM
  19(7), 385–394, DOI 10.1145/360248.360252. Checked the published paper at
  https://lim.univ-reunion.fr/staff/fred/Enseignement/Verif-M2/Articles/Autres/Symbolic-execution-and-Program-Testing-King-1976.pdf.
- Baldoni, Coppa, D'Elia, Demetrescu, and Finocchi (2018), "A Survey of Symbolic
  Execution Techniques", ACM Computing Surveys 51(3), article 50, 39 pages,
  DOI 10.1145/3182657. Read the authors' manuscript at
  https://arxiv.org/abs/1610.00502; verified final publication metadata against
  the institutional record https://iris.luiss.it/handle/11385/192577.

The exceptional-input subsection now briefly explains safe and sAssert, including
assertions inserted by Data.SBV.Tools.Overflow. Provers/Prover.hs implements safe
by checking the registered assertions; Maybe.fromJust is a selector without an
assertion. Both Prover.hs and Overflow.hs are now included in validation hashes.
The companion checks that the raw Nothing selector produces no safety obligations,
that safe checkedFromJust returns a satisfiable violation whose model is Nothing,
and that an isJust constraint makes the registered assertion unsatisfiable.
The constrained Symbolic computation explicitly marks its result with output so
that the assertion is registered; merely returning an unevaluated symbolic term
would not exercise the check. Unknown or missing results cannot pass this check.

At this snapshot the rebuilt main PDF has 62 pages. The new symbolic-execution
subsection and safety example were visually checked; there are no overfull boxes
or undefined citations or references. HLint and the focused companion checks pass.

### 2026-11-10: dedicated safety-checking subsection

Promoted the short safety paragraph into "Checking safety with sAssert and safe"
after exceptional inputs. The subsection explains assertion obligations versus
assumptions, shows the already validated Nothing counterexample, and describes
how the isJust precondition discharges it. It retains the distinction between
checked arithmetic and operations that insert no assertions. No companion
implementation changed. At this snapshot the subsection is 11.2 on page 27;
the main PDF remains 62 pages, with no overfull boxes or unresolved references.

The safety subsection now prints the constrained example and its successful
result directly. The extracted safeFromJust helper reuses the existing check;
validation calls the same helper displayed in the paper. A sentence explains why
output registers the result for assertion checking. The PDF remains 62 pages.

Simplified the successful safety example to a direct safe call with sAssert
visible in the listing, next to the constrain assumption. The named IO helper
is now internal to the validation code; readers need not follow another function
call to find the assertion. Its body remains extracted from the checked source.

### 2026-11-10: AES as an example of what TP enables

Added one paragraph at the end of the conclusion, alongside the further-reading
examples, without a new section or proof walkthrough. This keeps the example's
point about what TP enables outside the teaching sequence. It contrasts the
earlier impractical one-shot SMT attempt
with the compositional AES-128 round-trip proof in Examples/TP/AES.hs. The claim
is specific to the previously unproved SBV example, not an assertion that AES
round-trip proofs were impossible in other systems. The new module proves the
original Crypto/AES.hs predicate for every 128-bit plaintext and key, using Z3
and CVC5; its full and recall-based doctests pass. This is a pointer to current
SBV development, not an example executed by the tutorial's pinned companion.

### 2026-11-10: nested recursion, productivity, and stream observations

Extended the termination subsection with McCarthy 91: its nested recursive
definition, the nonnegative measure max(0, 101-n), and the postcondition checked
alongside termination by smtFunctionWithContract. Added an Ackermann pointer.
The definitions and API claims were checked against Examples/TP/McCarthy91.hs,
Examples/TP/Ackermann.hs, and Core/Model.hs.

Added a productivity subsection immediately after finite lists and datatypes,
with the requested forward reference from the latter. It distinguishes
constructor-guardedness checking from termination and from the existence of an
infinite value in the solver's domain. NatStream and MutualCorecursion are
identified as examples of the API, not evidence that finite SMT sequences
provide a coinductive stream model. Index functions and terminating finite-prefix
generators offer representations for stream observations; proving their laws
does not establish productivity of a separate lazy implementation. This follows
the representation constraint recorded in
Artifacts/DesignExplorations/infinite-lists-and-coinduction.md. No new companion
checks or proof transcripts were added.

### 2026-11-10: standalone McCarthy 91 section

Moved McCarthy 91 into its own section after induction on decreasing measures.
The section explains why a result contract is needed for nested recursion and
shows the measure decrease for inputs at most 89 and for inputs from 90 through
100. It points to the existing correctness proof and Ackermann example. The
execution-model termination subsection now refers back to this section, and
the introduction roadmap includes it. No new executable example was added.

The section now prints the actual definition, specification, and guided
strong-induction case from the pinned McCarthy91 module. prepare.py extracts
the local case up to its explicit source boundary, retaining the existing
non-whitespace identity check. The companion's --mccarthy91 command runs the
library's complete correctness proof and rejects unchecked dependencies;
validate.py includes this command, checks the reported termination, and hashes
the library source. The focused check passes with a Proven result and
"Functions proven terminating: mcCarthy91". The companion builds with strict
warnings and HLint passes. The full validation suite subsequently passed,
including McCarthy 91, and results/validation.txt was refreshed with matching
input hashes. The PDF was rebuilt with the locally installed Tectonic binary;
there are no overfull boxes or undefined references.

### 2026-11-10: counterexample output spelling

SBV now prints Counterexample consistently. Updated the manuscript's displayed
transcripts and noted the spelling normalization under Following along. The
companion remains pinned to its validated snapshot, which prints Counter-example;
validate.py accepts both headers while retaining its independent model checks.
Raw execution logs retain the pinned library's actual output.
The snapshot pin is temporary: before submission, migrate to the next SBV
release, regenerate the execution log, and remove the manuscript's temporary
spelling-normalization note once the companion prints Counterexample itself.

### 2026-11-11: generated-code speed (AES benchmark)

Added "How fast is the generated code?" (section 22.3) at the end of the C-generation
section: one table and three short paragraphs. It reports the AES-128 reused-key benchmark in
`Artifacts/AES128Benchmark`: SBV-generated C against BearSSL `aes_big`, tiny-AES-c, and OpenSSL
(single-block and bulk). The explanation offered is code size: the generated encryptor is about four
times BearSSL's (2.5 KB code plus four 1 KB tables against 0.7 KB plus one table), with no round loop,
while BearSSL rotates a single table. The text says explicitly that table size and unrolling were not varied
independently, so this is consistent with the data but not an isolated cause. OpenSSL is presented as
hardware AES (ARM crypto extensions, `OPENSSL_armcap=0x87d`), a different class from portable C, and the
text does not generalize beyond one Apple M5 Pro with Apple Clang.

Honesty points carried from the benchmark review: the figures were measured at a 1-minute load average of
3.4 on 18 logical CPUs (the harness waits for a quarter of the CPUs, since the timed code is single-threaded);
the report states this. The first benchmark run had started at load 48, which is why the harness now gates on load.
The raw JSON no longer contains the host name. The SBV C was regenerated from a clean tracked tree at commit
64315b78d and was byte-identical to the saved files. The vendored trees were reduced from 707 to 102 files, each
verified against its recorded hash. The tutorial states that the benchmark and the development SBV checkout it
used are not part of the pinned companion; its figures are not reproduced by `validate.py`. The generated C is
checked against the FIPS-197 vector and three other implementations, not proved, and the section says so.

Added bibliography entries `bearssl`, `tinyaes`, `openssl`. tiny-AES-c has no known publication year, so the entry
uses "n.d." rather than an invented date. Open item: if the benchmark figures are kept for submission, re-run them
after re-pinning SBV so that the code generator matches the pinned release.
