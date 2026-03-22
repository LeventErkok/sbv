# SBV: SMT Based Verification in Haskell

[![Build Status](https://github.com/LeventErkok/sbv/actions/workflows/ci.yml/badge.svg)](https://github.com/LeventErkok/sbv/actions/workflows/ci.yml)

***Express properties about Haskell programs and automatically prove them using SMT solvers.***

[Hackage](http://hackage.haskell.org/package/sbv) | [Release Notes](http://github.com/LeventErkok/sbv/tree/master/CHANGES.md) | [Documentation](http://hackage.haskell.org/package/sbv/docs/Data-SBV.html)

SBV provides symbolic versions of Haskell types. Programs written with these types can be automatically verified, checked for satisfiability, optimized, or compiled to C — all via SMT solvers.

## SBV in 5 Minutes

Fire up GHCi with SBV:

```
$ cabal repl --build-depends sbv
```

For unbounded integers, `x + 1 .> x` is always true:

```haskell
ghci> :m Data.SBV
ghci> prove $ \x -> x + 1 .> (x :: SInteger)
Q.E.D.
```

But with machine arithmetic, overflow lurks:

```haskell
ghci> prove $ \x -> x + 1 .> (x :: SInt8)
Falsifiable. Counter-example:
  s0 = 127 :: Int8
```

IEEE-754 floats break reflexivity of equality:

```haskell
ghci> prove $ \x -> (x :: SFloat) .== x
Falsifiable. Counter-example:
  s0 = NaN :: Float
```

What's the multiplicative inverse of 3 modulo 256?

```haskell
ghci> sat $ \x -> x * 3 .== (1 :: SWord8)
Satisfiable. Model:
  s0 = 171 :: Word8
```

Use quantifiers for named results:

```haskell
ghci> sat $ skolemize $ \(Exists @"x" x) (Exists @"y" y) -> x * y .== (96::SInteger) .&& x + y .== 28
Satisfiable. Model:
  x = 24 :: Integer
  y =  4 :: Integer
```

Optimize a cost function subject to constraints:

```haskell
ghci> :{
optimize Lexicographic $ do x <- sInteger "x"
                            y <- sInteger "y"
                            constrain $ x + y .== 20
                            constrain $ x .>= 5
                            constrain $ y .>= 5
                            minimize "cost" $ x * y
:}
Optimal in an extension field:
  x    =  5 :: Integer
  y    = 15 :: Integer
  cost = 75 :: Integer
```

For inductive proofs and equational reasoning, SBV includes a theorem prover:

```haskell
revApp :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> Forall "ys" [a] -> SBool))
revApp = induct "revApp"
                 (\(Forall xs) (Forall ys) -> reverse (xs ++ ys) .== reverse ys ++ reverse xs) $
                 \ih (x, xs) ys -> [] |- reverse ((x .: xs) ++ ys)
                                      =: reverse (x .: (xs ++ ys))
                                      =: reverse (xs ++ ys) ++ [x]
                                      ?? ih
                                      =: (reverse ys ++ reverse xs) ++ [x]
                                      =: reverse ys ++ (reverse xs ++ [x])
                                      =: reverse ys ++ reverse (x .: xs)
                                      =: qed
```

```
ghci> runTP $ revApp @Integer
Inductive lemma: revApp
  Step: Base                            Q.E.D.
  Step: 1                               Q.E.D.
  Step: 2                               Q.E.D.
  Step: 3                               Q.E.D.
  Step: 4                               Q.E.D.
  Step: 5                               Q.E.D.
  Result:                               Q.E.D.
Functions proven terminating: sbv.reverse
[Proven] revApp :: Ɐxs ∷ [Integer] → Ɐys ∷ [Integer] → Bool
```

## Features

**Symbolic types** — Booleans, signed/unsigned integers (8/16/32/64-bit and arbitrary-width), unbounded integers, reals, rationals, IEEE-754 floats, characters, strings, lists, tuples, sums, optionals, sets, enumerations, and uninterpreted sorts. User-defined algebraic data types (including enumerations, recursive, and parametric types) are supported via `mkSymbolic`, with pattern matching via `sCase`:

```haskell
{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}

import Data.SBV

data Expr a = Val a
            | Add (Expr a) (Expr a)
            | Mul (Expr a) (Expr a)
            deriving Show

-- Make Expr symbolically available, named SExpr
mkSymbolic [''Expr]

eval :: SymVal a => (SBV a -> SBV a -> SBV a) -> (SBV a -> SBV a -> SBV a) -> SBV (Expr a) -> SBV a
eval add mul = smtFunction "eval" $ \e ->
    [sCase| e of
       Val v   -> v
       Add x y -> eval add mul x `add` eval add mul y
       Mul x y -> eval add mul x `mul` eval add mul y
    |]

```

**Verification** — `prove`/`sat`/`allSat` for property checking and model finding, `safe`/`sAssert` for assertion verification, `dsat`/`dprove` for delta-satisfiability, and QuickCheck integration.

**Optimization** — Minimize/maximize cost functions subject to constraints via `optimize`/`maximize`/`minimize`, with support for lexicographic, independent, and Pareto objectives.

**Quantifiers and functions** — Universal and existential quantifiers (including alternating), with skolemization for named bindings. Define SMT-level functions directly from Haskell via `smtFunction`, including recursive and mutually recursive definitions with automatic termination checking.

**Theorem proving (TP)** — Semi-automated inductive proofs (including strong induction) with equational reasoning chains. Includes termination checking, recursive and mutually recursive definitions, productive (co-recursive) functions, and user-defined measures.

**Code generation** — Compile symbolic programs to C as straight-line programs or libraries (`compileToC`, `compileToCLib`), and generate test vectors (`genTest`).

**SMT interaction** — Incremental mode via `runSMT`/`query` for programmatic solver interaction with a high-level typed API. Run multiple solvers simultaneously with `proveWithAny`/`proveWithAll`.

## Supported SMT Solvers

SBV communicates with solvers via the standard SMT-Lib interface:

| Solver | From | | Solver | From |
|--------|------|-|--------|------|
| [ABC](http://www.eecs.berkeley.edu/~alanmi/abc) | Berkeley | | [DReal](http://dreal.github.io/) | CMU |
| [Bitwuzla](http://bitwuzla.github.io/) | Stanford | | [MathSAT](http://mathsat.fbk.eu/) | FBK / Trento |
| [Boolector](http://boolector.github.io/) | JKU | | [OpenSMT](http://verify.inf.usi.ch/opensmt) | USI |
| [CVC4](http://cvc4.github.io/) | Stanford / Iowa | | [Yices](http://github.com/SRI-CSL/yices2) | SRI |
| [CVC5](http://cvc5.github.io/) | Stanford / Iowa | | [Z3](http://github.com/Z3Prover/z3/wiki) | Microsoft |

**Z3** is the default solver. Use `proveWith`, `satWith`, etc. to select a different one (e.g., `proveWith cvc5`). See [tested versions](http://github.com/LeventErkok/sbv/blob/master/SMTSolverVersions.md) for details. Other SMT-Lib compatible solvers can be hooked up with minimal effort — get in touch if you'd like to use one not listed here.

## A Selection of Examples

SBV ships with many worked examples. Here are some highlights:

| Example | Description |
|---------|-------------|
| [Sudoku](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-Puzzles-Sudoku.html) | Solve Sudoku puzzles using SMT constraints |
| [N-Queens](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-Puzzles-NQueens.html) | Solve the N-Queens placement puzzle |
| [SEND + MORE = MONEY](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-Puzzles-SendMoreMoney.html) | The classic cryptarithmetic puzzle |
| [Fish/Zebra](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-Puzzles-Fish.html) | Einstein's logic puzzle |
| [SQL Injection](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-Strings-SQLInjection.html) | Find inputs that cause SQL injection vulnerabilities |
| [Regex Crossword](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-Strings-RegexCrossword.html) | Solve regex crossword puzzles |
| [BitTricks](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-BitPrecise-BitTricks.html) | Verify bit-manipulation tricks from Stanford's bithacks collection |
| [Legato multiplier](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-BitPrecise-Legato.html) | Correctness proof of Legato's 8-bit multiplier |
| [Prefix sum](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-BitPrecise-PrefixSum.html) | Ladner-Fischer prefix-sum implementation proof |
| [AES](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-Crypto-AES.html) | AES encryption with C code generation |
| [CRC](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-CodeGeneration-CRC_USB5.html) | Symbolic CRC computation with C code generation |
| [Sqrt2 irrational](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-TP-Sqrt2IsIrrational.html) | Prove that the square root of 2 is irrational |
| [Sorting](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-TP-InsertionSort.html) | Prove [insertion sort](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-TP-InsertionSort.html), [merge sort](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-TP-MergeSort.html), and [quick sort](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-TP-QuickSort.html) correct |
| [Kadane](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-TP-Kadane.html) | Prove Kadane's maximum segment-sum algorithm correct |
| [McCarthy91](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-TP-McCarthy91.html) | Prove McCarthy's 91 function meets its specification |
| [Binary search](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-TP-BinarySearch.html) | Prove binary search correct |
| [Collatz](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-TP-Collatz.html) | Explore properties of the Collatz sequence |
| [Infinitely many primes](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-TP-Primes.html) | Prove there are infinitely many primes |
| [Tautology checker](http://hackage.haskell.org/package/sbv/docs/Documentation-SBV-Examples-TP-TautologyChecker.html) | A verified BDD-style tautology checker |

Browse the full collection in `Documentation.SBV.Examples` [on Hackage](http://hackage.haskell.org/package/sbv).

## License

SBV is distributed under the [BSD3](http://en.wikipedia.org/wiki/BSD_licenses) license. See [COPYRIGHT](http://github.com/LeventErkok/sbv/tree/master/COPYRIGHT) and [LICENSE](http://github.com/LeventErkok/sbv/tree/master/LICENSE) for details.

Please report bugs and feature requests at the [GitHub issue tracker](http://github.com/LeventErkok/sbv/issues).

## Thanks

The following people made major contributions to SBV, by developing new features and contributing to the design in significant ways: Joel Burget, Brian Huffman, Brian Schroeder, and Jeffrey Young.

The following people reported bugs, provided comments/feedback, or contributed to the development of SBV in various ways:
Andreas Abel,
Ara Adkins,
Andrew Anderson,
Kanishka Azimi,
Markus Barenhoff,
Reid Barton,
Ben Blaxill,
Ian Blumenfeld,
Guillaume Bouchard,
Martin Brain,
Ian Calvert,
Oliver Charles,
Christian Conkle,
Matthew Danish,
Iavor Diatchki,
Alex Dixon,
Robert Dockins,
Thomas DuBuisson,
Trevor Elliott,
Gergő Érdi,
John Erickson,
Richard Fergie,
Adam Foltzer,
Joshua Gancher,
Remy Goldschmidt,
Jan Grant,
Brad Hardy,
Tom Hawkins,
Greg Horn,
Jan Hrcek,
Georges-Axel Jaloyan,
Anders Kaseorg,
Tom Sydney Kerckhove,
Lars Kuhtz,
Piërre van de Laar,
Pablo Lamela,
Ken Friis Larsen,
Andrew Lelechenko,
Joe Leslie-Hurd,
Nick Lewchenko,
Brett Letner,
Sirui Lu,
Georgy Lukyanov,
Martin Lundfall,
Daniel Matichuk,
John Matthews,
Curran McConnell,
Philipp Meyer,
Fabian Mitterwallner,
Joshua Moerman,
Matt Parker,
Jan Path,
Matt Peddie,
Lucas Peña,
Matthew Pickering,
Lee Pike,
Gleb Popov,
Rohit Ramesh,
Geoffrey Ramseyer,
Blake C. Rawlings,
Jaro Reinders,
Stephan Renatus,
Dan Rosén,
Ryan Scott,
Eric Seidel,
Austin Seipp,
Andrés Sicard-Ramírez,
Don Stewart,
Greg Sullivan,
Josef Svenningsson,
George Thomas,
May Torrence,
Daniel Wagner,
Sean Weaver,
Robin Webbers,
Eddy Westbrook,
Nis Wegmann,
Jared Ziegler,
and Marco Zocca.

Thanks!
