# SBV: SMT Based Verification in Haskell

[![Build Status](https://github.com/LeventErkok/sbv/actions/workflows/haskell-ci.yml/badge.svg)](https://github.com/LeventErkok/sbv/actions/workflows/haskell-ci.yml)

On Hackage: http://hackage.haskell.org/package/sbv

Express properties about Haskell programs and automatically prove them using SMT solvers.

On one end, SBV can be used as a push-button prover over many types:

```haskell
$ ghci
ghci> :m Data.SBV
ghci> prove $ \x -> x `shiftL` 2 .== 4 * (x::SWord8)
Q.E.D.
ghci> prove $ \x -> x `shiftL` 2 .== 2 * (x::SWord8)
Falsifiable. Counter-example:
  s0 = 32 :: Word8
```

On the other extreme, SBV can be used as an SMT-based proof assistant to prove equational and inductive program properties:

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

Running this proof produces:

```haskell
ghci> runTP $ revApp @Integer
Inductive lemma: revApp
  Step: Base                            Q.E.D.
  Step: 1                               Q.E.D.
  Step: 2                               Q.E.D.
  Step: 3                               Q.E.D.
  Step: 4                               Q.E.D.
  Step: 5                               Q.E.D.
  Result:                               Q.E.D.
[Proven] revApp :: Ɐxs ∷ [Integer] → Ɐys ∷ [Integer] → Bool
```

Establishing how `reverse` distributes over `++` (at the monomorpic type of list of integers).

The function `prove` establishes theorem-hood, while `sat` finds a satisfying model if it exists. The `runTP` function
runs a proof script, establishing theorems with user guidance.

All satisfying models can be computed using `allSat`.
SBV can also perform static assertion checks, such as absence of division-by-0, and other user given properties.
Furthermore, SBV can perform optimization, minimizing/maximizing arithmetic goals for their optimal values.

SBV also allows for an incremental mode: Users are given a handle to the SMT solver as their programs execute, and they can issue SMTLib commands programmatically, query values, and direct the interaction using a high-level typed API. The incremental mode also allows for creation of constraints based on the current model, and access to internals of SMT solvers for advanced users. See the `runSMT` and `query` commands for details.

## Overview

 - [Hackage](http://hackage.haskell.org/package/sbv)
 - [Release Notes](http://github.com/LeventErkok/sbv/tree/master/CHANGES.md)
   
SBV library provides support for dealing with symbolic values in Haskell. It introduces the types:

 - `SBool`: Symbolic Booleans (bits).
 - `SWord8`, `SWord16`, `SWord32`, `SWord64`: Symbolic Words (unsigned).
 - `SInt8`, `SInt16`, `SInt32`, `SInt64`: Symbolic Ints (signed).
 - `SWord N`, `SInt N`, for `N > 0`: Arbitrary sized unsigned/signed bit-vectors, parameterized by the bitsize. (Using DataKinds extension.)
 - `SInteger`: Symbolic unbounded integers (signed).
 - `SReal`: Symbolic infinite precision algebraic reals (signed).
 - `SRational`: Symbolic rationals, ratio of two symbolic integers. (`Rational`.)
 - `SFloat`: IEEE-754 single precision floating point number. (`Float`.)
 - `SDouble`: IEEE-754 double precision floating point number. (`Double`.)
 - `SFloatingPoint`: IEEE-754 floating point number with user specified exponent and significand sizes. (`FloatingPoint`)
 - `SChar`: Symbolic characters, supporting unicode.
 - `SString`: Symbolic strings.
 - `SList`: Symbolic lists. (Which can be nested, i.e., lists of lists.)
 - `STuple`: Symbolic tuples (upto 8-tuples, can be nested)
 - `SEither`: Symbolic sums
 - `SMaybe`: Symbolic optional values
 - `SSet`: Symbolic sets
 - Arrays of symbolic values.
 - Symbolic enumerations, for arbitrary user-defined enumerated types.
 - Symbolic polynomials over GF(2^n ), polynomial arithmetic, and CRCs.
 - Uninterpreted constants and functions over symbolic values, with user defined axioms.
 - Uninterpreted sorts, and proofs over such sorts, potentially with axioms.
 - Ability to define SMTLib functions, generated directly from Haskell versions, including support for recursive and mutually recursive functions.
 - Reasoning with universal and existential quantifiers, including alternating quantifiers.
   
The user can construct ordinary Haskell programs using these types, which behave like ordinary Haskell values when used concretely. However, when used with symbolic arguments, functions built out of these types can also be:

 - proven correct via an external SMT solver (the `prove` function),
 - checked for satisfiability (the `sat`, and `allSat` functions),
 - checked for assertion violations (the `safe` function with `sAssert` calls),
 - checked for delta-satisfiability (the `dsat` and `dprove` functions),
 - used in synthesis (the `sat`function with existentials),
 - checked for machine-arithmetic overflow/underflow conditions,
 - optimized with respect to cost functions (the `optimize`, `maximize`, and `minimize` functions),
 - quick-checked,
 - used for generating Haskell and C test vectors (the `genTest` function),
 - compiled down to C, rendered as straight-line programs or libraries (`compileToC` and `compileToCLib` functions).
   
## Picking the SMT solver to use

The SBV library uses third-party SMT solvers via the standard SMT-Lib interface. The following solvers are supported:

 - [ABC](http://www.eecs.berkeley.edu/~alanmi/abc) from University of Berkeley
 - [Boolector](http://boolector.github.io/) from Johannes Kepler University
 - [Bitwuzla](http://bitwuzla.github.io/) from Stanford University
 - [CVC4](http://cvc4.github.io/) from Stanford University and the University of Iowa
 - [CVC5](http://cvc5.github.io/) from Stanford University and the University of Iowa
 - [DReal](http://dreal.github.io/) from CMU
 - [MathSAT](http://mathsat.fbk.eu/) from FBK and DISI-University of Trento
 - [OpenSMT](http://verify.inf.usi.ch/opensmt) from Università della Svizzera italiana
 - [Yices](http://github.com/SRI-CSL/yices2) from SRI
 - [Z3](http://github.com/Z3Prover/z3/wiki) from Microsoft
   
Most functions have two variants: For instance `prove`/`proveWith`. The former uses the default solver, which is currently Z3. The latter expects you to pass it a configuration that picks the solver.
The valid values are `abc`, `boolector`, `bitwuzla`, `cvc4`, `cvc5`, `dReal`, `mathSAT`, `openSMT`, `yices`, and `z3`.

See [versions](http://github.com/LeventErkok/sbv/blob/master/SMTSolverVersions.md) for a listing of the versions of these tools SBV has been tested with. Please report if you see any discrepancies!

Other SMT solvers can be used with SBV as well, with a relatively easy hook-up mechanism. Please do get in touch if you plan to use SBV with any other solver.

## Using multiple solvers, simultaneously

SBV also allows for running multiple solvers at the same time, either picking the result of the first to complete, or getting results from all.
See `proveWithAny`/`proveWithAll` and `satWithAny`/`satWithAll` functions. The function `sbvAvailableSolvers` can be used to query the available solvers at run-time.

## TP: Semi-automated theorem proving

While SMT solvers are quite powerful, there is a certain class of problems that they are just not well suited for. In particular, SMT
solvers are not good at proofs that require induction, or those that require complex chains of reasoning. Induction is necessary to reason about
any recursive algorithm, and most such proofs require carefully constructed equational steps.

SBV allows for a style of semi-automated theorem proving, called TP. which can be used to construct such proofs.
The documentation includes example proofs for many list functions, and even inductive proofs for
the familiar insertion, merge, quick-sort algorithms, along with a proof that the square-root of 2 is irrational.
While a proper theorem prover (such as Lean, Isabelle etc.) is a more appropriate choice for such proofs, with some
guidance (and acceptance of a much larger trusted code base!), SBV can be used to establish correctness of various mathematical
claims and algorithms that are usually beyond the scope of SMT solvers alone. See the documentation under
the `Documentation.SBV.Examples.TP` directory.

## Copyright, License

The SBV library is distributed with the BSD3 license. See [COPYRIGHT](http://github.com/LeventErkok/sbv/tree/master/COPYRIGHT) for details.
The [LICENSE](http://github.com/LeventErkok/sbv/tree/master/LICENSE) file contains the [BSD3](http://en.wikipedia.org/wiki/BSD_licenses) verbiage.

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
Nis Wegmann,
Jared Ziegler,
and Marco Zocca.

Thanks!
