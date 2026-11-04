# Editorial notes

## Target and format

Haskell Symposium 2027, tutorial category. The [2026 call](https://icfp26.sigplan.org/home/haskellsymp-2026#Call-for-Papers-and-Talks) evaluates tutorials on
whether they explain an aspect of Haskell or its ecosystem in a generally useful
way; they need not report original research. Tutorials are limited to 25 pages
in single-column `acmsmall`, must be labeled as such in the subtitle, and are
reviewed lightweight double-blind. The 2026 call does not explicitly exempt
references: counting them toward the limit is our working assumption, not a
confirmed 2027 rule. On 4 November 2026, the [ICFP 2027 site](https://icfp27.sigplan.org/)
listed no Haskell Symposium call, and a search found none. Re-check the tutorial
limit and treatment of references when that call appears.
Pass 1 reduced the draft from 27 to 26 pages while adding datatype induction.
Pass 2 adds troubleshooting and two teaching figures, with reserve cuts bringing
the draft to 25 pages including references.
The completeness listing, closures, and related-tools reserve cuts are already
included in that count. The standalone package now lets "Following along" use
two Cabal commands instead of repository instructions, imports, and extension
setup, freeing space for Pass 3. With all six exercises now included, the paper
remains 25 pages including references. The final prose pass retains that count,
with little remaining margin.
All previously listed reserve cuts have now been used.
The `nonacm` class option suppresses dummy DOI, price, and publication metadata;
remove it and insert the assigned metadata for publication. The 2026 call
explicitly recommends `review` and specifies `[acmsmall,screen]`; it says
nothing about `nonacm`. Its acceptability for review remains unconfirmed.
Re-check all three points (references, `review`, `nonacm`) against the 2027 call.
The 2026 call requires supplementary material to be uploaded separately at
submission time, rather than linked from the paper to an external repository.

## Structure

| Section | Teaches | Companion listings |
|---|---|---|
| 1 Introduction | Audience, roadmap, pinned standalone package, runnable setup | Cabal commands |
| 2 First proofs | Symbolic types, dotted operators, `ite`, quantification, vacuity | (inline transcripts) |
| 3 Specifications | Independent specs; a refuted wrong guard | `saturating`, `wrongAdd` |
| 4 Finding values | `allSat` | `idempotent` |
| 5 Optimization | Objective measures, lexicographic/box/Pareto modes, extension-field bounds, strict-bound and nonlinear limitations | `production`, `realBounds` |
| 6 Haskell vs symbolic structure | Host lists, `SList`, `smtFunction`, bounded automatic attempt | `hostSum`, `sumL`, `sumWithoutInduction` |
| 7 Programming the solver | `query` descent loop, dependency synchronization | `descent` |
| 8 Symbolic datatypes | `mkSymbolic`, `sCase`, synthesis by `sat` | `expr` |
| 9 Arrays and symbolic memory | Functional updates, extensional equality, aliasing, bounds, infinite index domains | `writesCommute` |
| 10 Proofs by induction | `induct`, proof types, calculations, hints, generalization | `sumNonNeg`, `revAcc`, `revWeak`, `revAccCorrect`, `reverseCorrect` |
| 11 Kadane (detailed) | Independent segment oracle, spec, implementation, three-case invariant figure, proof | `mss`, `segmentOracle`, `kadane`, `kadaneCorrect` |
| 12 Induction over datatypes | Size measure, smaller-child lemmas, both child hypotheses; analogous multiplication case abbreviated | `exprMirror`, `mirrorCorrect` |
| 13 Polymorphic and higher-order proofs | Monomorphic instances, bookkeeping law, uninterpreted operations, conditional algebraic laws, explicit closure environments | `reverseLength`, `listProofImports`, `bookKeeping`, `bookKeepingRun`, `closure` |
| 14 Tautology checker (overview) | Lexicographic measures, strong induction beyond children, proof architecture | library quotes |
| 15 C generation | `compileToC`, validating the translation boundary | `codegen` |
| 16 Under the hood | Deferred nodes, sharing, run contexts, synchronization, termination obligations, finite-data semantics | (inline) |
| 17 Pitfalls and trust | Troubleshooting by outcome, diagnostics and replay, random testing, trusted base | `inspectSatAdd`; companion `testSatAdd` |
| 18 Related tools | QuickCheck, Rosette, Grisette, Smten, what4, Liquid Haskell, Dafny | — |

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

## Revision rationale

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
claim-support problem remains. Raw fetched metadata and extracted text are kept
locally under `build/reference-audit/` (not distributed in the supplement).
The corrected bibliography was rebuilt and inspected in the 25-page PDF, with
no final-pass overfull boxes or undefined references. All 11 executable input
hashes still match `results/validation.txt`; this audit changes citations and
editorial documentation. The companion source archive was regenerated.

## Open items for the author

The approved personal acknowledgments thank Joel Burget, Iavor Diatchki,
Brian Huffman, John Matthews, Brian Schroeder, Jeffrey Young, and the wider SBV
community. They are in `acks`, hidden in the anonymous PDF; omit that environment
from the anonymized review source archive and retain it for camera-ready.

- Re-check the 2027 Haskell Symposium call when published: tutorial page limit,
  reference counting, class options, disclosure placement, and supplement rules.
- Finish the anonymized supplement from the standalone source package. Its
  validation log contains identifying local paths that should be removed for
  anonymous review. Restore the companion copyright holder and TeX author for
  camera-ready.
- SBV 14.10 release-day changes: retain `sbv ==14.10`; remove the
  `source-repository-package` stanza from `cabal.project`, including the
  identifying `https://github.com/LeventErkok/sbv.git` URL; update source
  discovery for extraction/validation; regenerate the freeze file; and
  revalidate against the Hackage release. Then remove the Git prerequisite and
  the paper's and bibliography's source-snapshot wording, and regenerate the
  supplement. The current Git pin stays until that migration is validated.
- Decide whether the tutorial should mention Cryptol/SAW or other users of SBV.
  The text currently makes no adoption claims.
- AI-disclosure work is deferred at the author's request.
  The manuscript's Preparation paragraph currently discloses the
  Codex assistance documented here. Check the final wording against the 2027
  venue rules. ACM's authorship-policy page returned HTTP 403 on 4 November
  2026; the [official SIGCSE TS 2027 policy page](https://2027.sigcse-ts.acm.org/info/policies-ai)
  quotes ACM's updated distinction: writing assistance alone needs no disclosure,
  while AI used in substantive research work and artifact development must be
  described in the methods. Our visible preparation paragraph records both;
  this tutorial has no separate methods section. This is not a claim that the
  Haskell Symposium has adopted SIGCSE-specific rules.
