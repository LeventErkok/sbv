# SBV TP Rewrite Combinator — Design Notes

**WARNING: These are rough design ideas, NOT a ready-to-implement specification.**
The soundness story here is incomplete and needs serious scrutiny before any
implementation work begins. When picking this up, the FIRST step should be to
rigorously work out the exact soundness conditions — what invariants must hold,
what can go wrong, what the solver actually guarantees vs. what we're assuming.
The ideas below are a starting point for discussion, not a blueprint.

## Motivation

The Huffman optimality proof exposed a fundamental limitation of SBV's theorem proving
infrastructure: **SMT solvers verify but don't rewrite**. The solver receives complex
expressions involving nested `smtFunction` applications and must discover simplifications
from axioms. It consistently fails when multiple recursive functions with different
recursive structures interact (e.g., `lightW` follows the lighter child while `sibW`
follows the deeper child).

Isabelle/HOL handles these proofs easily because its `simp` tactic **rewrites** terms
using proved equalities before the decision procedure sees them. We need an analogous
capability in SBV's TP system.

## The Problem in Detail

### What works
The SMT solver is excellent at:
- Verifying inequalities between explicit ITE expressions
- Unfolding a single recursive function one level
- Checking concrete instances (e.g., `Bin(Tip, Tip)` base cases)
- Combining 2-3 simple facts in a single step

### What fails
The solver consistently chokes on:
- **Cross-function recursive reasoning**: `lightW + light2W <= deepW + sibW` requires
  understanding that `lightW` (follows lighter child) and `deepW` (follows deeper child)
  traverse different paths but the sum inequality holds.
- **List reconstruction**: `head(xs) .: tail(xs) = xs` combined with function substitution
  (e.g., `treeWeight(head(leavesOf t)) = lightW t`).
- **Nested smtFunction applications**: 3+ levels of nesting (e.g., `collapse(swap(..., relabelFrom 0 t))`)
  overwhelm the solver regardless of how many hints are provided.
- **Chaining 4+ facts**: Even when each fact is provided as a proof hint, the solver
  can't chain more than ~3 steps of reasoning in one go.

### Concrete examples from the Huffman proof

1. **`bhFirstStepLW`**: The solver has `bhFirstStep` (about `treeWeight(head(...))`) and
   `lightWIsHead` (connecting `lightW t = treeWeight(head(leavesOf t))`), but can't
   substitute one into the other to get the combined result in terms of `lightW`.

2. **`minPairSum`**: The solver has IH on subtrees and `light2WLeqMaxLightW`, but can't
   bridge `light2W(Bin l r)` (which follows the lighter child's subtree) with
   `sibW(Bin l r)` (which follows the deeper child's subtree) even with case splits.

3. **`optMerge` properties**: `optMerge t` wraps `collapse(swapFourSyms(relabelFrom 0 t, ...))`.
   Even as an opaque `smtFunction`, properties like `cost(optMerge t) + lightW + light2W <= cost t`
   require the solver to unfold `optMerge` and chain swap-cost + collapse-cost lemmas.

## Proposed Solution: DAG-Level Rewrite Combinator

### Key Insight

SBV's internal representation is a hash-consed DAG of `SVal` nodes. When we write
`lightW t`, this creates a single DAG node (an uninterpreted function application).
The Haskell function body is gone — it was executed to BUILD the node.

However, proved equalities give us pairs of `SVal` nodes that are semantically equal.
We can mechanically substitute one for the other in any expression, at the DAG level,
without involving the SMT solver.

### The `rewrite` Combinator

```haskell
-- In a proof chain, rewrite the current expression using a proved equality
=: rewrite (lwIsHead `at` Inst @"t" t)
-- Mechanically replaces all occurrences of lightW(t) with treeWeight(head(leavesOf(t)))
-- in the current goal expression. No SMT call needed.
```

### Implementation

#### Step 1: User provides LHS, RHS, and proof

**Do NOT try to extract LHS/RHS/condition from the SVal representation.**
The internal SVal for a conditional equality like `A => B = C` compiles to
`OR (NOT A) (EQ B C)`, and pattern-matching on this is fragile (optimizer rewrites,
distribution, flattening, etc.). Inequalities don't even have an `EQ` node.

Instead, the user provides LHS and RHS as Haskell expressions, and the proof as evidence:

```haskell
=: rewrite (lightW t) (treeWeight (head (leavesOf t))) (lwIsHead `at` Inst @"t" t)
--         ^^^ lhs    ^^^ rhs                           ^^^ proof that lhs = rhs
```

SBV evaluates both Haskell expressions to get `SVal` nodes `N1` (for `lightW t`)
and `N2` (for `treeWeight(head(leavesOf t))`). These are concrete DAG nodes —
no decomposition of the proof's internal SVal needed.

#### Step 2: Substitute in the goal DAG

Since `SVal` is hash-consed, finding `lhs` is pointer comparison (O(1) per node).
Walk the goal DAG and replace every occurrence of `lhs` with `rhs`.

```haskell
substSVal :: SVal -> SVal -> SVal -> SVal
substSVal lhs rhs goal = walk goal
  where
    walk n
      | n == lhs  = rhs           -- pointer equality (hash-consed)
      | isLeaf n  = n
      | otherwise = rebuild n (map walk (children n))
```

The `rebuild` function reconstructs the DAG node with substituted children,
going through the hash-consing infrastructure to maintain sharing.

#### Step 3: Integrate into proof chains

```haskell
-- New proof step type
data ProofStep = ...
    | Rewrite Proof  -- rewrite using this proved equality

-- In the proof chain:
|- lightW t + light2W t .<= deepW t + sibW t
=: rewrite (lwIsHead `at` Inst @"t" t)
-- Goal becomes: treeWeight(head(leavesOf t)) + light2W t <= deepW t + sibW t
=: rewrite (l2wIsSecond `at` Inst @"t" t)
-- Goal becomes: treeWeight(head(leavesOf t)) + treeWeight(head(tail(leavesOf t))) <= deepW t + sibW t
=: sTrue   -- NOW the solver handles explicit head/tail expressions
=: qed
```

### Soundness

**Critical: conditional equalities.** Most proved equalities are of the form `A => B = C`,
not just `B = C`. The rewrite `B → C` is only valid when condition `A` holds in the
current proof context. Applying it unconditionally would be unsound.

The `rewrite` step must:
1. Extract the condition `A`, the LHS `B`, and the RHS `C` from the proved equality
2. **Verify that `A` holds** in the current context before performing the substitution
3. Only then replace `B` with `C` in the goal

#### How to verify the condition

Since we don't extract the condition from the SVal, we use a different approach:
after performing the substitution `G[lhs] → G[rhs]`, verify soundness with a single
SMT call:

**Check:** `G[lhs] AND proof_assertion => G[rhs]`

Where `proof_assertion` is the instantiated proof added to the solver context.
If the proof is `A => lhs = rhs`, and `A` holds (from intros), then `lhs = rhs`
is in context, and `G[lhs] => G[rhs]` follows by congruence.

If `A` does NOT hold, the proof only gives `NOT A OR (lhs = rhs)`, which doesn't
force `lhs = rhs`, and the implication `G[lhs] => G[rhs]` may fail. The solver
detects this and the rewrite is rejected.

This is a SINGLE cheap SMT call that:
- Verifies the condition holds (implicitly, by checking the implication)
- Verifies the substitution is correct (the right nodes were replaced)
- Doesn't require pattern-matching on the proof's internal SVal structure

```haskell
-- Pseudocode for the rewrite step:
rewriteStep lhs rhs proof currentGoal intros = do
    let lhsVal = unSBV lhs
        rhsVal = unSBV rhs
        newGoal = substitute lhsVal rhsVal currentGoal
        proofAssertion = instantiateProof proof
    -- Quick SMT check: old goal + proof => new goal
    valid <- checkImplication (currentGoal .&& proofAssertion) newGoal intros
    unless valid $
        error "rewrite: condition not satisfied or substitution incorrect"
    return newGoal
```

This is much cheaper than the original proof step because the solver only needs
to verify a simple implication (with the equality already in context), not discover
the entire chain of reasoning.

#### Unconditional equalities

For unconditional equalities (`B = C` with no condition), the rewrite is always valid.
No condition check needed. Examples: `lightWIsHead` (`lightW t = treeWeight(head(leavesOf t))`
with no precondition) can be applied freely.

#### Nested conditions

Some equalities have multiple conditions: `A1 && A2 && A3 => B = C`. Each condition
must be verified independently. The system should check all of them before rewriting.

### What This Solves

| Sorry step | Why it's stuck | How rewrite fixes it |
|---|---|---|
| `bhFirstStepLW` | Solver can't substitute `lightW t → treeWeight(head(leavesOf t))` | `rewrite lwIsHead`, `rewrite l2wIsSecond`, then `bhFirstStep` matches directly |
| `minPairSum` | Cross-recursive functions (`lightW` vs `sibW`) | Unfold both sides one level via rewrite, solver sees explicit ITEs |
| `light2WIsSecond` | `insertAll`/`sortedInsert` reasoning on merged lists | Rewrite using IH + `lightWIsHead`, reduce to structural list equality |
| `optMergeCost` | Deeply nested `optMerge` expression | Rewrite `optMerge(t)` using its definition (one level), then apply swap/collapse cost lemmas via further rewrites |
| `optMergeLeavesOf` | Same nesting issue | Rewrite + apply `leavesOfSwap` and `collapseLeavesOf` step by step |

### Design Considerations

#### Hash-consing and node identity
SBV's `SVal` uses hash-consing, so structurally identical expressions share the same
node. This means `lightW t` always produces the same `SVal` node for a given `t`,
making the find-and-replace operation reliable and efficient.

#### Directionality
A proved equality `a = b` can be applied left-to-right (`a → b`) or right-to-left (`b → a`).
The combinator should support both:
```haskell
=: rewrite (lwIsHead `at` t)         -- lightW t → treeWeight(head(leavesOf t))
=: rewriteRev (lwIsHead `at` t)      -- treeWeight(head(leavesOf t)) → lightW t
```

#### Composability
Multiple rewrites should be chainable cheaply:
```haskell
=: rewrite rule1    -- microseconds (DAG walk)
=: rewrite rule2    -- microseconds (DAG walk)
=: rewrite rule3    -- microseconds (DAG walk)
=: sTrue            -- one SMT call on the simplified expression
=: qed
```

Each rewrite is O(|goal DAG|) with no solver overhead. The solver only processes
the final simplified form.

#### Function unfolding as a special case
"Unfolding" an `smtFunction` one level is just rewriting with the function's definition:
```haskell
-- If lightW is defined as smtFunction "lightW" $ \t -> [sCase| t of Tip w _ -> w; Bin l r -> ite (...) |]
-- Then for a known Bin l r (from pCase):
=: unfold lightW    -- rewrites lightW(Bin l r) → ite(lightW l <= lightW r, lightW l, lightW r)
```

This requires storing the original Haskell lambda alongside the smtFunction,
or re-evaluating it at the specific argument.

## Alternative / Complementary Features

### Custom induction schemes
Allow defining induction rules that case-split on domain-specific conditions
(not just the datatype constructor). For example, an induction rule for
`lightW`/`sibW` interaction that splits on both `lightW l <= lightW r` AND
`height l >= height r` simultaneously.

### Congruence reasoning
Explicit `f(a) = f(b)` steps when `a = b` is known. Currently the solver
should handle this via the congruence closure algorithm, but it sometimes
fails with deeply nested function applications.

## Relationship to the Huffman Proof

The Huffman optimality proof (Isabelle-style) has a clean skeleton that closes
modulo sorry. The remaining sorry steps are:

1. `light2WIsSecond` — 3 non-TipTip cases
2. `optMergeTreeSize` — treeSize(optMerge t) < treeSize t
3. `optMergeNumLeaves` — numLeaves(optMerge t) >= 2
4. `optMergeCost` — cost(optMerge t) + lightW + light2W <= cost t
5. `optMergeLeavesOf` — leavesOf(optMerge t) = shorter list
6. `bhFirstStepLW` — BH cost = lightW + light2W + BH(shorter)
7. `minPairSum` — lightW + light2W <= deepW + sibW

Each of these would be closeable with the rewrite combinator, as they all
involve substituting proved equalities or unfolding function definitions —
operations the SMT solver can't do but DAG-level rewriting handles trivially.

## References

- Blanchette, Jasmin Christian. "An Isabelle/HOL Formalization of the Textbook
  Proof of Huffman's Algorithm." Archive of Formal Proofs, 2008.
  (The Isabelle proof we're following; uses `simp` extensively for rewriting)
- The SBV TP infrastructure: `Data/SBV/TP/Kernel.hs`, `Data/SBV/TP/Utils.hs`
- Internal SVal representation: `Data/SBV/Core/Symbolic.hs`
