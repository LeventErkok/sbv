# Infinite Lists & Coinduction in TP — Design Exploration

*Explored interactively by Levent Erkok with Claude (Opus 4.8, 1M context), as a brainstorming session.*

**Status:** Explored, **shelved**. Not recommended for implementation.
**Date:** 2026-06-12

**Question:** Can/should TP reason about infinite (and partial) lists, given that `SList a` is the
SMT `Seq` sort (finite sequences)?

**Bottom line:** No. Heavy, research-grade machinery; thin demand; and real soundness exposure (in a
*prover*, a subtle bug means proving false things). At best we'd land a flaky corner of what
Isabelle/Dafny already do with far more infrastructure.

---

## 1. The grounding constraint

`SList a` is an SMT `Seq` — **finite** sequences. No `⊥`, no partial lists, no infinite values.
TP's `induct` is finite structural induction, so a TP theorem `∀ (xs :: SList a). P xs` holds for
**finite lists only**. Canonical trap if one forgets this: `reverse (reverse xs) ≡ xs` is provable
for finite lists but **false** for infinite ones (`reverse [1..] = ⊥`).

---

## 2. Approaches considered, and why each is not right

### 2a. `⊥`-lifting / Scott induction — sound but not viable
Reframe an infinite list as the lub of partial approximations (`⊥ ⊑ x0:⊥ ⊑ …`) and prove `P` by
`⊥`-base induction (`P(⊥)` + cons-step) instead of `[]`-base. This is sound, and it correctly blocks
unsound lifts (e.g. `revRev` fails because its helper `revApp` is false at `⊥`, on the strictness of
`++`). **Why not:**
- Requires a sound per-argument-position **strictness analyzer** (one wrong slot ⇒ the prover proves
  false things), a **`Total`-tag trust chain** on proofs/hints, and a coherent `⊥`/partial-list
  **domain model** layered over a logic that has no `⊥`.
- **Fatal:** there are no infinite `SList` values to *apply* the resulting theorem to. The only
  "infinite lists" are productive `define-fun-rec`s, which the solver can't reason about anyway. The
  deliverable is a theorem about a domain SBV can neither express nor consume.

### 2b. Take-lemma coinduction — clean reduction, blocked by the solver
Define `s ≅ t := ∀n. take n s ≡ take n t` and prove by induction on `n` — reducing coinduction to
finite-list + ℕ-induction, never needing infinite values to exist. **Why not:** the per-step goals
proved **empirically too hard for cvc5 and (especially) z3**, for two compounding reasons:
1. solvers won't reliably **unfold a `define-fun-rec` once**;
2. the **sequence theory** (`take`/`subList`/`++` with symbolic `n`) is a known soft spot.
The take lemma lands on both at once.

### 2c. General coinduction is intrinsically hard and risky
Even dedicated provers struggle: Coq's native coinduction is painful enough that the **Paco** library
exists; Agda's ergonomic sized-types route has had **soundness holes**; Isabelle's good story
(`codatatype`/BNF) took a multi-year research program; Lean punts (`Stream' = ℕ → α`); Dafny made it
work on Z3 only via dedicated language support (prefix predicates). For an SMT-tactic layer on finite
`Seq`, "rock-solid" is not realistically attainable.

---

## 3. The only viable route, if ever revisited

Represent streams as **index functions `Nat → a`**, *not* as `Seq`:
- Equality becomes pointwise: `s ≅ t := ∀i. s i ≡ t i` — a plain first-order `∀i` goal. No `take`, no
  `subList`, no `define-fun-rec`-over-`Seq`.
- Uniform laws are trivial: `map f s = λi. f (s i)`, so `map f (map g s) ≅ map (f∘g) s` is reflexivity.
- **Sweet spot = what `sEnum`/`enumFrom` produce:** an arithmetic stream is `λi. base + i·step`
  (closed form), so properties become `∀i` arithmetic goals — which the solvers handle well.

Limits: corecursive streams without a closed index form become recursive over `Nat` (back to
induction, but friendlier than `Seq`); non-uniform/structural ops (`filter`, etc.) are awkward-to-
impossible. So this covers only the **uniform fragment** (map/zip/enumerations) — which barely
overlaps with "general infinite-list theorem proving," but is the only slice with positive ROI and a
real chance of being sound.

---

## 4. Triggers to revisit
- A concrete user with real infinite-list proof obligations.
- Reliable recursive-/coinductive-`Seq` reasoning (or first-class codata) arriving in the SMT backend.

If picked up, take route §3 (index functions, uniform fragment). Do **not** pursue §2a or §2b.
