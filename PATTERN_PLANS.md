# Plan: Add `:pattern`-Annotated Quantified Hints to SBV TP

## Context

The Huffman optimality proof gets stuck because SMT solvers don't eagerly unfold
`define-fun-rec` definitions. The solver has `lightW(Tip w s) = w` as a recursive
definition but won't instantiate it when it sees `lightW(Tip sw ss)` in the goal.
Adding ground hints (`?? proof \`at\` ...`) doesn't help because the solver can't
chain through the unfolded forms to verify sortedInsert preconditions, list length
properties, etc.

SMTLib `:pattern` annotations on quantified assertions trigger **E-matching**: the
solver eagerly instantiates the axiom whenever it sees the pattern term in its
E-graph. This effectively gives us "rewrite rules" without building DAG-level
rewrite infrastructure.

## The Problem (Concrete)

In the Huffman proof, we keep hitting this pattern:

```haskell
-- Solver has hint: lightW r = treeWeight(head(leavesOf r))
-- Solver has hint: sortedInsertPrepend says sortedInsert a xs = a .: xs when treeWeight a <= treeWeight(head xs)
-- Solver has cases condition: lightW l <= lightW r
-- Goal needs: treeWeight(sTip (sweight l) 0) <= treeWeight(head(leavesOf r))
--
-- Chain needed: treeWeight(sTip (sweight l) 0) = sweight l = lightW l <= lightW r = treeWeight(head(leavesOf r))
-- The solver CANNOT chain this because it won't unfold treeWeight(Tip w s) = w or lightW(Tip w s) = w
```

With `:pattern` annotations, the solver would automatically instantiate
`treeWeight(Tip w s) = w` whenever it sees `treeWeight(Tip _ _)`, giving it
the missing link.

## Key Insight: How SBV Represents Quantified Assertions

`QuantifiedBool` (in `Data/SBV/Core/Symbolic.hs:227`) stores **pre-generated SMTLib text**:

```haskell
| QuantifiedBool T.Text  -- stores e.g. "(forall ((w Int) (s Int)) (= (lightW (Tip w s)) w))"
```

In `SMTLib2.hs:860`:
```haskell
sh (SBVApp (QuantifiedBool i) []) = i  -- just emits the stored text directly
```

So the text passes through unchanged. To add `:pattern`, we just need to generate
different text:
```
(forall ((w Int) (s Int)) (! (= (lightW (Tip w s)) w) :pattern ((lightW (Tip w s)))))
```

The `:pattern` wraps the BODY inside the forall as `(! body :pattern (terms))`.

## How `constraintGen` Works (Lambda.hs:243-256)

```haskell
constraintGen scope trans inState f = do
   liftIO $ modifyIORef' rProgInfo (\u -> u{hasQuants = True})
   let mkDef (Defn deps _frees Nothing       body) = trans deps body
       mkDef (Defn deps _frees (Just params) body) = trans deps $ \i ->
           T.unwords (map mkGroup params) <> "\n"
           <> body (i + 2)
           <> T.replicate (length params) ")"
       mkGroup (ALL, s) = "(forall " <> s
       mkGroup (EX,  s) = "(exists " <> s
   inSubState scope inState $ \st -> mkDef <$> convert st KBool (mkConstraint st f >>= output >> pure ())
```

The `body (i + 2)` is the quantified formula body as SMTLib text. To add a pattern,
we'd change this to: `"(! " <> body (i + 2) <> " :pattern (" <> patternText <> "))"`.

## How Hints Flow: `??` → `constrain` → SMTLib

1. User writes `?? proof \`at\` Inst @"t" r`
2. `instantiate` (TP.hs:1196) extracts proposition, applies to concrete args → ground `SBool`
3. The `SBool` becomes `HelperProof ProofObj` in the proof step
4. During `smtProofStep` (Kernel.hs:295), helpers are processed:
   - `constrain (getObjProof helper)` adds the proposition to solver context
5. The proposition (possibly quantified via `quantifiedBool`) goes through normal `constrain` pipeline
6. Ends up as `(assert <text>)` in SMTLib

For a **non-instantiated** proof (used without `at`), the proposition retains its
`Forall` quantifiers, and `quantifiedBool` generates the `(forall ...)` text. This
already works today — we just need to add the `:pattern` annotation.

## Implementation Plan

### Step 1: Modify `constraintGen` in `Data/SBV/Lambda.hs`

Add an optional pattern parameter. Create a variant:

```haskell
-- Alongside constraint (line 265):
constraintWithPattern :: (MonadIO m, Constraint (SymbolicT m) a)
                      => State -> a -> T.Text -> m SV
constraintWithPattern st prop patternText =
    join . constraintGenWithPattern TopLevel mkSV st prop patternText
  where mkSV _deps d = liftIO $ newExpr st KBool (SBVApp (QuantifiedBool (d 0)) [])

constraintGenWithPattern :: ... => LambdaScope -> trans -> State -> a -> T.Text -> m b
constraintGenWithPattern scope trans inState f patternText = do
   -- Same as constraintGen but wrap body with (! body :pattern (patternText))
   let mkDef (Defn deps _frees (Just params) body) = trans deps $ \i ->
           T.unwords (map mkGroup params) <> "\n"
           <> "(! " <> body (i + 4) <> "\n"
           <> T.replicate (i + 4) " " <> ":pattern (" <> patternText <> "))"
           <> T.replicate (length params) ")"
       ...
```

**But**: the `patternText` needs to reference the same bound variables as the body.
The pattern expression must be evaluated in the same `inSubState` context so it
references the same symbolic variables.

**Better approach**: have the user provide the pattern as part of the same function
that generates the proposition body. Inside `inSubState`, evaluate both.

### Step 2: Create `quantifiedBoolWithPattern` in `Data/SBV/Lambda.hs`

```haskell
-- New export:
quantifiedBoolWithPattern :: (Constraint Symbolic a, ...) => a -> (freshVars -> SBV b) -> SBool
```

The trick: the `a` in `Constraint Symbolic a` is the proposition function (e.g.,
`\(Forall @"w" w) (Forall @"s" s) -> lightW (sTip w s) .== w`). The pattern
function has the same argument structure.

**Simplest implementation**: modify `constraintGen` to accept a callback that,
given the State with the fresh variables already created, produces the pattern text.

```haskell
constraintGen' :: ... => LambdaScope -> trans -> State -> a -> Maybe (State -> IO T.Text) -> m b
```

When the `Maybe` is `Just`, after converting the body, call the pattern callback
with the same State (which has the bound variables) to get the pattern text, then
wrap the body.

### Step 3: User-facing API in `Data/SBV/TP/TP.hs`

```haskell
-- New helper variant (extend Helper data type, line 1228):
data Helper = ...
            | HelperPatternHint SBool  -- pattern-annotated quantified bool

-- New function:
withPattern :: (Constraint Symbolic prop, Constraint Symbolic pat)
            => prop -> pat -> Helper
withPattern proposition patternExpr = HelperPatternHint $
    quantifiedBoolWithPattern proposition patternExpr
```

Add `HintsTo` instance so it works with `??`:
```haskell
instance HintsTo a Helper where
  addHint x h = ...
```

(This instance likely already exists — `HelperPatternHint` just needs to be
handled in `getAllHelpers` / proof step processing.)

### Step 4: Process in `smtProofStep` (Kernel.hs)

In the helper processing (around line 370), handle `HelperPatternHint`:

```haskell
-- When processing helpers:
case helper of
  HelperPatternHint sbool -> constrain sbool  -- the SBool already has forall+pattern baked in
  ...
```

Since the `SBool` from Step 2 already contains the `QuantifiedBool` with the
pattern text embedded, normal `constrain` handles it — the text passes through
`cvtExp` unchanged (line 860).

### Step 5: No changes to `SMTLib2.hs`

The `:pattern` annotation is already in the `QuantifiedBool` text. No backend changes.

## Detailed File Changes

| File | Lines | Change |
|------|-------|--------|
| `Data/SBV/Lambda.hs` | ~243-270 | Add `constraintGenWithPattern` variant (or modify `constraintGen` with optional pattern param) |
| `Data/SBV/Lambda.hs` | new | Export `quantifiedBoolWithPattern` |
| `Data/SBV/TP/TP.hs` | ~1228 | Add `HelperPatternHint SBool` to `Helper` |
| `Data/SBV/TP/TP.hs` | new | Add `withPattern` function |
| `Data/SBV/TP/TP.hs` | ~1234-1260 | Handle `HelperPatternHint` in helper extraction |
| `Data/SBV/TP/Kernel.hs` | ~360-370 | Handle `HelperPatternHint` in proof step processing |

**Estimated total: ~70-100 lines of new/modified code.**

## Tricky Bit: Sharing Variables Between Proposition and Pattern

The proposition and pattern must reference the **same** bound variables. When
`constraintGen` calls `inSubState`, it creates fresh symbolic variables for the
`Forall` parameters. The pattern function must be evaluated in this same substate.

**Solution**: Package both into a single function that's evaluated in one `inSubState` call:

```haskell
quantifiedBoolWithPattern :: ... => (args -> SBool) -> (args -> SBV patternType) -> SBool
```

Inside the implementation:
1. Enter `inSubState` (creates fresh variables for `Forall` params)
2. Apply `args -> SBool` to get the body SVal
3. Apply `args -> SBV patternType` to get the pattern SVal
4. Convert pattern SVal to SMTLib text (via `lambdaStr` or similar)
5. Wrap body with `(! body :pattern (pattern_text))`
6. Store in `QuantifiedBool`

The type-level challenge: the proposition function type is `Forall "w" Integer -> Forall "s" Integer -> SBool`,
while the pattern function type is `Forall "w" Integer -> Forall "s" Integer -> SHTree` (or whatever
the pattern expression's type is). These have different return types but the same argument structure.

**Practical solution**: Use a combined function that returns a tuple:
```haskell
withPattern' :: (args -> (SBool, SBV a)) -> Helper
withPattern' combined = ...
```

Or use two separate functions and thread through the same State.

## User Workflow for Huffman Proof

```haskell
-- 1. Prove one-level unfolding lemmas (trivial, each is one unfolding):
lwTip <- lemma "lwTip"
    (\(Forall @"w" w) (Forall @"s" s) -> lightW (sTip w s) .== w) []

twTip <- lemma "twTip"
    (\(Forall @"w" w) (Forall @"s" s) -> treeWeight (sTip w s) .== w) []

siPrepend <- recall sortedInsertPrependProof  -- already proved

-- 2. In the proof, use them as pattern-triggered axioms:
?? withPattern (\(Forall @"w" w) (Forall @"s" s) -> lightW (sTip w s) .== w)
              (\(Forall @"w" w) (Forall @"s" s) -> lightW (sTip w s))

?? withPattern (\(Forall @"w" w) (Forall @"s" s) -> treeWeight (sTip w s) .== w)
              (\(Forall @"w" w) (Forall @"s" s) -> treeWeight (sTip w s))

-- 3. Now sortedInsert lemmas fire automatically because the solver
--    can chain: treeWeight(Tip w s) = w = lightW(Tip w s) = lightW l
```

## What This Solves

| Stuck step | Why it's stuck | How patterns fix it |
|---|---|---|
| TB1c, TB2c, BT1c | Can't verify sortedInsert prepend condition | `treeWeight(Tip w s) = w` pattern fires, gives solver the weight equality |
| BB cases | Can't connect lightW to sweight | `lightW(Tip w s) = w` pattern fires |
| optMergeCost | Can't chain through relabel/swap | Patterns for `relabelCost`, `swapPreservesHeight` etc. fire |
| optMergeLeavesOf | Same deep composition issue | Patterns for `leavesOfSwap`, `collapseLeavesOf` fire |

## Testing

1. Add infrastructure (Steps 1-4)
2. Test with ONE simple case: prove `lightW(Tip w s) = w`, add as pattern hint,
   verify a previously-stuck step now closes
3. If it works: add pattern hints for all needed unfoldings (~10-15 trivial lemmas)
4. Run the full `light2WIsSecondProof` — should close with pattern hints
5. Tackle `optMergeCost` and `optMergeLeavesOf` with similar pattern hints

## Risks

1. **Pattern placement**: Must be `(forall (vars) (! body :pattern (trigger)))` —
   the `!` wraps the BODY inside the forall, not the whole assertion.
2. **Variable sharing**: Pattern and body must reference the same bound variables.
   Implementation must evaluate both in the same `inSubState` call.
3. **E-matching loops**: Unlikely for one-level unfoldings, but theoretically possible.
   No mitigation needed initially.
4. **Solver compatibility**: z3 and cvc5 both support `:pattern`. Documented in SMT-LIB 2.6.

## Soundness Argument

The emitted axiom is a proved lemma — already verified by the solver in a prior step.
Adding it again as a quantified assertion with `:pattern` is logically redundant (the
`define-fun-rec` already encodes the same information). The `:pattern` annotation is
purely a search hint — it doesn't change the logical content. Therefore:

- If the lemma proof is correct, the axiom is correct.
- The pattern only affects WHEN the solver instantiates, not WHAT it instantiates.
- No new logical content is introduced.

The main risk is implementation bugs in the text generation (emitting wrong variable
bindings or wrong pattern text). Mitigated by inspecting SMTLib output with `transcript`.
