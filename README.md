# SBV: SMT Based Verification in Haskell

[![Build Status](https://github.com/LeventErkok/sbv/actions/workflows/ci.yml/badge.svg)](https://github.com/LeventErkok/sbv/actions/workflows/ci.yml)

***Express properties about Haskell programs and automatically prove them using SMT solvers.***

[Hackage](http://hackage.haskell.org/package/sbv) | [Release Notes](http://github.com/LeventErkok/sbv/tree/master/CHANGES.md) | [Documentation](http://hackage.haskell.org/package/sbv/docs/Data-SBV.html)

SBV turns Haskell into a verification-aware language. Write ordinary Haskell functions using symbolic types, then prove properties, find counterexamples, or generate C code — all backed by SMT solvers.

```haskell
$ ghci
ghci> :m Data.SBV
ghci> prove $ \x -> x `shiftL` 2 .== 4 * (x::SWord8)
Q.E.D.
ghci> prove $ \x -> x `shiftL` 2 .== 2 * (x::SWord8)
Falsifiable. Counter-example:
  s0 = 32 :: Word8
```

For problems beyond the reach of push-button SMT (induction, equational reasoning), SBV provides a semi-automated theorem prover:

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

**Symbolic types** — Booleans, signed/unsigned integers (8/16/32/64-bit and arbitrary-width), unbounded integers, reals, rationals, IEEE-754 floats, characters, strings, lists, tuples, sums, optionals, sets, enumerations, algebraic data types, and uninterpreted sorts.

**Verification** — `prove`/`sat`/`allSat` for property checking and model finding, `safe`/`sAssert` for assertion verification, `dsat`/`dprove` for delta-satisfiability, `optimize`/`maximize`/`minimize` for optimization, and QuickCheck integration.

**Theorem proving (TP)** — Semi-automated inductive proofs with equational reasoning chains. Includes termination checking, recursive and mutually recursive definitions, productive (co-recursive) functions, and user-defined measures.

**Code generation** — Compile symbolic programs to C as straight-line programs or libraries (`compileToC`, `compileToCLib`), and generate test vectors (`genTest`).

**SMT interaction** — Incremental mode via `runSMT`/`query` for programmatic solver interaction with a high-level typed API. Run multiple solvers simultaneously with `proveWithAny`/`proveWithAll`.

## Supported SMT Solvers

SBV communicates with solvers via the standard SMT-Lib interface:

| Solver    | From                                                          |
|-----------|---------------------------------------------------------------|
| ABC       | [Berkeley](http://www.eecs.berkeley.edu/~alanmi/abc)          |
| Boolector | [Johannes Kepler University](http://boolector.github.io/)     |
| Bitwuzla  | [Stanford University](http://bitwuzla.github.io/)             |
| CVC4      | [Stanford / Iowa](http://cvc4.github.io/)                     |
| CVC5      | [Stanford / Iowa](http://cvc5.github.io/)                     |
| DReal     | [CMU](http://dreal.github.io/)                                |
| MathSAT   | [FBK / University of Trento](http://mathsat.fbk.eu/)          |
| OpenSMT   | [USI](http://verify.inf.usi.ch/opensmt)                       |
| Yices     | [SRI](http://github.com/SRI-CSL/yices2)                      |
| Z3        | [Microsoft](http://github.com/Z3Prover/z3/wiki)              |

**Z3** is the default solver. Use `proveWith`, `satWith`, etc. to select a different one (e.g., `proveWith cvc5`). See [tested versions](http://github.com/LeventErkok/sbv/blob/master/SMTSolverVersions.md) for details. Other SMT-Lib compatible solvers can be hooked up with minimal effort — get in touch if you'd like to use one not listed here.

## Getting Started

Install from Hackage:

```
$ cabal install sbv
```

Then try it in GHCi:

```haskell
$ ghci
ghci> :m Data.SBV
ghci> sat $ \x -> x * x .== (1089::SInteger)
Satisfiable. Model:
  s0 = 33 :: Integer
```

For examples, see the `Documentation.SBV.Examples` modules [on Hackage](http://hackage.haskell.org/package/sbv).

## Theorem Proving

SBV's TP module supports semi-automated theorem proving for problems that require induction or complex equational reasoning — areas where push-button SMT solving falls short.

Key capabilities:
- Inductive proofs over recursive data structures
- Equational reasoning with calculational proof chains
- Recursive and mutually recursive function definitions with termination checking
- Productive (co-recursive) function definitions
- User-defined termination measures with automatic verification

The documentation includes proofs of sorting algorithm correctness (insertion sort, merge sort, quick sort), irrationality of the square root of 2, properties of the Collatz sequence, and many more. See the `Documentation.SBV.Examples.TP` modules [on Hackage](http://hackage.haskell.org/package/sbv) for the full collection.

## License

SBV is distributed under the [BSD3](http://en.wikipedia.org/wiki/BSD_licenses) license. See [COPYRIGHT](http://github.com/LeventErkok/sbv/tree/master/COPYRIGHT) and [LICENSE](http://github.com/LeventErkok/sbv/tree/master/LICENSE) for details.

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
