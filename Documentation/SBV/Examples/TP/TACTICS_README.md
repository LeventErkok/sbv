# Tactic-Based Theorem Proving Interface for SBV

## Overview

This implementation adds a **tactic-based proof interface** to SBV's TP (Theorem Proving) module, complementing the existing calculational proof style. The implementation works within SBV's architectural constraints: since formulas are opaque handles to the SMT solver (no AST inspection), the tactics focus on **proof state management** rather than formula manipulation.

## Key Files

1. **Data/SBV/TP/Tactics.hs** - Core tactic infrastructure
2. **Documentation/SBV/Examples/TP/TacticStyle.hs** - Usage examples

## Design Philosophy

Unlike traditional tactic systems (Coq, Lean, Isabelle) that can inspect and transform formula ASTs, SBV's tactics operate at a higher level:

- **Context Management**: Track assumptions and available lemmas
- **Goal Stack Manipulation**: Organize subgoals to prove
- **Solver Invocation**: Delegate actual proving to SMT solver with appropriate context
- **Proof Structuring**: Provide composable proof scripts for complex proofs

## Core Types

```haskell
-- A goal to be proven
data Goal = Goal
  { goalId      :: Int
  , goalName    :: String
  , goalClaim   :: SBool
  , goalContext :: [(String, SBool)]  -- assumptions
  }

-- Proof state
data ProofState = ProofState
  { psGoals      :: [Goal]              -- goal stack
  , psLemmas     :: [ProofObj]          -- available lemmas
  , psGlobalCtx  :: [(String, SBool)]   -- global assumptions
  , ...
  }

-- A tactic transforms proof state
type Tactic = ProofState -> TP (Either String ProofState)
```

## Main Tactics

### Basic Tactics
- `auto` - Invoke SMT solver to prove current goal
- `autoUsing` - Prove using specific lemmas
- `using` - Add lemmas to context

### Goal Manipulation
- `focus` - Focus on specific goal
- `swap` - Swap first two goals
- `defer` - Move current goal to end
- `rotate` - Rotate goal stack

### Case Analysis
- `splitOn` - Split goal into cases (user-provided conditions)
- `considerCases` - Split and apply different tactics to each case

### Tactic Combinators
- `>>` - Sequential composition
- `tryTactic` - Try without failing
- `tryAll` - Try multiple tactics, take first success
- `allGoals` - Apply tactic to all goals

## Usage Examples

###Simple Proof
```haskell
simpleTactic :: IO (Proof (Forall "x" Integer -> SBool))
simpleTactic = runTP $
  theorem "simple"
          (\(Forall x) -> x .> 0 .=> x + 1 .> 1)
          auto
```

### Case Analysis
```haskell
caseSplit :: IO (Proof (Forall "n" Integer -> SBool))
caseSplit = runTP $
  theorem "cases"
          (\(Forall n) -> sAbs n .>= 0) $
    splitOn [ ("n_positive", n .>= 0)
            , ("n_negative", n .<  0)
            ] >>
    allGoals auto
```

### Using Lemmas
```haskell
withHelper :: TP (Proof (Forall "x" Integer -> SBool))
withHelper = do
  helper <- theorem "helper" (\(Forall x) -> x + 1 .> x) auto

  theorem "main"
          (\(Forall x) -> x .>= 0 .=> x + 1 .> 0) $
    using [helper] >> auto
```

## Comparison: Calculational vs Tactic Style

### Calculational Style (existing)
```haskell
calc "example"
     (\(Forall x) -> x + 1 .> x) $
     \x -> [] |- x + 1
            =: x + 1
            =: qed
```

**Pros:**
- Natural for equational reasoning
- Shows explicit derivation steps
- Good for mathematical calculations

**Cons:**
- Can get deeply nested
- Less composable

### Tactic Style (new)
```haskell
theorem "example"
        (\(Forall x) -> x + 1 .> x)
        auto
```

**Pros:**
- More composable (tactics are values)
- Better for case analysis
- Explicit goal state
- Familiar to Coq/Lean users

**Cons:**
- Doesn't show calculation steps
- Requires understanding combinators

## Limitations

Due to SBV's opaque formula representation, these tactics **cannot**:

- Inspect formula structure (no pattern matching on `SBool`)
- Automatically determine how to split cases
- Perform syntactic rewriting
- Implement tactics like `intro`, `destruct`, `inversion` from Coq

These tactics **can**:

- Manage proof assumptions and lemmas
- Organize complex case analyses (with user guidance)
- Compose proof strategies
- Provide better error messages via goal tracking

## Implementation Notes

1. **No Exception Handling**: The current implementation doesn't catch proof failures. If `auto` fails, the entire tactic fails. This could be enhanced with proper exception handling.

2. **Proof Generation**: Tactics ultimately delegate to the existing `calc`/`lemma` infrastructure for actual proof generation. The tactic layer is primarily organizational.

3. **Goal Tracking**: The `ProofState` explicitly tracks goals, which isn't strictly necessary for SBV's backend but provides better user feedback.

4. **Composability**: Tactics are first-class values, making it easy to build custom proof strategies by composing basic tactics.

## Future Enhancements

Possible improvements:

1. **Better Error Handling**: Catch exceptions from failed proofs
2. **Proof Search**: Implement `autoUsing` with automatic lemma selection
3. **Backtracking**: Add backtracking search for proof strategies
4. **Interactive Mode**: Allow step-by-step proof development
5. **Proof State Inspection**: Better tools for examining current goals
6. **Custom Tactics**: DSL for users to define their own tactics

## Conclusion

This tactic-based interface provides an alternative proof style for SBV that emphasizes:
- **Composability** over derivation details
- **Goal management** over formula manipulation
- **Proof scripts** over proof terms

It complements rather than replaces the existing calculational style, giving users choice in how they structure their proofs.
