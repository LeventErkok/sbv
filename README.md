SBV: Symbolic Bit Vectors in Haskell
====================================

Express and properties about bit-precise Haskell programs and automatically prove
them using SMT solvers.

Overview
========
The Haskell sbv library provides support for dealing with Symbolic Bit Vectors
in Haskell. It introduces the types:

  - SBool: symbolic booleans
  - SWord8, SWord16, SWord32, SWord64: Symbolic counterparts of Words (unsigned)
  - SInt8,  SInt16,  SInt32,  SInt64: Symbolic counterparts of Ints (signed)
  - Arrays of symbolic values

The user can construct ordinary Haskell programs using these types, which behave
very similar to their concrete counterparts. However, the predicates (i.e., functions
that return SBool) built out of these types can be:

  - proven correct via an external SMT solver (the "prove" function)
  - checked for satisfiability (the "sat" and "allSat" functions)
  - quick-checked

If a predicate is not valid, the prove function will return a counterexample: An 
assignment to inputs such that the predicate fails. For a satisfiability
check via the sat function, the library will return a satisfying assignment, if
there is one. The allSat function returns all satisfying assignments, lazily.

The library communicates with SMT solvers via the SMT-Lib interface:
     
        http://goedel.cs.uiowa.edu/smtlib/

While the library is designed to work with any SMT-Lib compliant SMT-solver,
solver specific support is required for parsing counter-example/model data since
there is currently no agreed upon format for getting models from arbitrary SMT
solvers. (The SMT-Lib2 initiative will potentially address this issue in the
future, at which point the sbv library can be generalized as well.)
Currently, we only support the Yices SMT solver from SRI as far as the counter-example
and model generation support is concerned:

        http://yices.csl.sri.com/

You should download and install Yices on your machine, and make sure the
"yices" executable is in your path before using the sbv library.

Please see the files under the Data/SBV/Examples directory for a number of
interesting applications and use cases.

Installation
============
The sbv library is cabalized. Assuming you have cabal/ghc installed, it should merely
be a matter of running cabal. Please see the INSTALL file for installation details.

Copyright, License
==================
The sbv library is distributed with the BSD3 license. See the COPYRIGHT file for
details. The LICENSE file contains the BSD3 verbiage.
