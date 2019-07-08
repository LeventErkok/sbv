-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.CodeGeneration.Fibonacci
-- Copyright : (c) Lee Pike
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Computing Fibonacci numbers and generating C code. Inspired by Lee Pike's
-- original implementation, modified for inclusion in the package. It illustrates
-- symbolic termination issues one can have when working with recursive algorithms
-- and how to deal with such, eventually generating good C code.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.CodeGeneration.Fibonacci where

import Data.SBV
import Data.SBV.Tools.CodeGen

-----------------------------------------------------------------------------
-- * A naive implementation
-----------------------------------------------------------------------------

-- | This is a naive implementation of fibonacci, and will work fine (albeit slow)
-- for concrete inputs:
--
-- >>> map fib0 [0..6]
-- [0 :: SWord64,1 :: SWord64,1 :: SWord64,2 :: SWord64,3 :: SWord64,5 :: SWord64,8 :: SWord64]
--
-- However, it is not suitable for doing proofs or generating code, as it is not
-- symbolically terminating when it is called with a symbolic value @n@. When we
-- recursively call @fib0@ on @n-1@ (or @n-2@), the test against @0@ will always
-- explore both branches since the result will be symbolic, hence will not
-- terminate. (An integrated theorem prover can establish termination
-- after a certain number of unrollings, but this would be quite expensive to
-- implement, and would be impractical.)
fib0 :: SWord64 -> SWord64
fib0 n = ite (n .== 0 .|| n .== 1)
             n
             (fib0 (n-1) + fib0 (n-2))

-----------------------------------------------------------------------------
-- * Using a recursion depth, and accumulating parameters
-----------------------------------------------------------------------------

{- $genLookup
One way to deal with symbolic termination is to limit the number of recursive
calls. In this version, we impose a limit on the index to the function, working
correctly upto that limit. If we use a compile-time constant, then SBV's code generator
can produce code as the unrolling will eventually stop.
-}

-- | The recursion-depth limited version of fibonacci. Limiting the maximum number to be 20, we can say:
--
-- >>> map (fib1 20) [0..6]
-- [0 :: SWord64,1 :: SWord64,1 :: SWord64,2 :: SWord64,3 :: SWord64,5 :: SWord64,8 :: SWord64]
--
-- The function will work correctly, so long as the index we query is at most @top@, and otherwise
-- will return the value at @top@. Note that we also use accumulating parameters here for efficiency,
-- although this is orthogonal to the termination concern.
--
-- A note on modular arithmetic: The 64-bit word we use to represent the values will of course
-- eventually overflow, beware! Fibonacci is a fast growing function..
fib1 :: SWord64 -> SWord64 -> SWord64
fib1 top n = fib' 0 1 0
  where fib' :: SWord64 -> SWord64 -> SWord64 -> SWord64
        fib' prev' prev m = ite (m .== top .|| m .== n)          -- did we reach recursion depth, or the index we're looking for
                                prev'                            -- stop and return the result
                                (fib' prev (prev' + prev) (m+1)) -- otherwise recurse

-- | We can generate code for 'fib1' using the 'genFib1' action. Note that the
-- generated code will grow larger as we pick larger values of @top@, but only linearly,
-- thanks to the accumulating parameter trick used by 'fib1'. The following is an excerpt
-- from the code generated for the call @genFib1 10@, where the code will work correctly
-- for indexes up to 10:
--
-- > SWord64 fib1(const SWord64 x)
-- > {
-- >   const SWord64 s0 = x;
-- >   const SBool   s2 = s0 == 0x0000000000000000ULL;
-- >   const SBool   s4 = s0 == 0x0000000000000001ULL;
-- >   const SBool   s6 = s0 == 0x0000000000000002ULL;
-- >   const SBool   s8 = s0 == 0x0000000000000003ULL;
-- >   const SBool   s10 = s0 == 0x0000000000000004ULL;
-- >   const SBool   s12 = s0 == 0x0000000000000005ULL;
-- >   const SBool   s14 = s0 == 0x0000000000000006ULL;
-- >   const SBool   s17 = s0 == 0x0000000000000007ULL;
-- >   const SBool   s19 = s0 == 0x0000000000000008ULL;
-- >   const SBool   s22 = s0 == 0x0000000000000009ULL;
-- >   const SWord64 s25 = s22 ? 0x0000000000000022ULL : 0x0000000000000037ULL;
-- >   const SWord64 s26 = s19 ? 0x0000000000000015ULL : s25;
-- >   const SWord64 s27 = s17 ? 0x000000000000000dULL : s26;
-- >   const SWord64 s28 = s14 ? 0x0000000000000008ULL : s27;
-- >   const SWord64 s29 = s12 ? 0x0000000000000005ULL : s28;
-- >   const SWord64 s30 = s10 ? 0x0000000000000003ULL : s29;
-- >   const SWord64 s31 = s8 ? 0x0000000000000002ULL : s30;
-- >   const SWord64 s32 = s6 ? 0x0000000000000001ULL : s31;
-- >   const SWord64 s33 = s4 ? 0x0000000000000001ULL : s32;
-- >   const SWord64 s34 = s2 ? 0x0000000000000000ULL : s33;
-- >   
-- >   return s34;
-- > }
genFib1 :: SWord64 -> IO ()
genFib1 top = compileToC Nothing "fib1" $ do
        x <- cgInput "x"
        cgReturn $ fib1 top x

-----------------------------------------------------------------------------
-- * Generating a look-up table
-----------------------------------------------------------------------------

{- $genLookup
While 'fib1' generates good C code, we can do much better by taking
advantage of the inherent partial-evaluation capabilities of SBV to generate
a look-up table, as follows.
-}

-- | Compute the fibonacci numbers statically at /code-generation/ time and
-- put them in a table, accessed by the 'select' call. 
fib2 :: SWord64 -> SWord64 -> SWord64
fib2 top = select table 0
  where table = map (fib1 top) [0 .. top]

-- | Once we have 'fib2', we can generate the C code straightforwardly. Below
-- is an excerpt from the code that SBV generates for the call @genFib2 64@. Note
-- that this code is a constant-time look-up table implementation of fibonacci,
-- with no run-time overhead. The index can be made arbitrarily large,
-- naturally. (Note that this function returns @0@ if the index is larger
-- than 64, as specified by the call to 'select' with default @0@.)
--
-- > SWord64 fibLookup(const SWord64 x)
-- > {
-- >   const SWord64 s0 = x;
-- >   static const SWord64 table0[] = {
-- >       0x0000000000000000ULL, 0x0000000000000001ULL,
-- >       0x0000000000000001ULL, 0x0000000000000002ULL,
-- >       0x0000000000000003ULL, 0x0000000000000005ULL,
-- >       0x0000000000000008ULL, 0x000000000000000dULL,
-- >       0x0000000000000015ULL, 0x0000000000000022ULL,
-- >       0x0000000000000037ULL, 0x0000000000000059ULL,
-- >       0x0000000000000090ULL, 0x00000000000000e9ULL,
-- >       0x0000000000000179ULL, 0x0000000000000262ULL,
-- >       0x00000000000003dbULL, 0x000000000000063dULL,
-- >       0x0000000000000a18ULL, 0x0000000000001055ULL,
-- >       0x0000000000001a6dULL, 0x0000000000002ac2ULL,
-- >       0x000000000000452fULL, 0x0000000000006ff1ULL,
-- >       0x000000000000b520ULL, 0x0000000000012511ULL,
-- >       0x000000000001da31ULL, 0x000000000002ff42ULL,
-- >       0x000000000004d973ULL, 0x000000000007d8b5ULL,
-- >       0x00000000000cb228ULL, 0x0000000000148addULL,
-- >       0x0000000000213d05ULL, 0x000000000035c7e2ULL,
-- >       0x00000000005704e7ULL, 0x00000000008cccc9ULL,
-- >       0x0000000000e3d1b0ULL, 0x0000000001709e79ULL,
-- >       0x0000000002547029ULL, 0x0000000003c50ea2ULL,
-- >       0x0000000006197ecbULL, 0x0000000009de8d6dULL,
-- >       0x000000000ff80c38ULL, 0x0000000019d699a5ULL,
-- >       0x0000000029cea5ddULL, 0x0000000043a53f82ULL,
-- >       0x000000006d73e55fULL, 0x00000000b11924e1ULL,
-- >       0x000000011e8d0a40ULL, 0x00000001cfa62f21ULL,
-- >       0x00000002ee333961ULL, 0x00000004bdd96882ULL,
-- >       0x00000007ac0ca1e3ULL, 0x0000000c69e60a65ULL,
-- >       0x0000001415f2ac48ULL, 0x000000207fd8b6adULL,
-- >       0x0000003495cb62f5ULL, 0x0000005515a419a2ULL,
-- >       0x00000089ab6f7c97ULL, 0x000000dec1139639ULL,
-- >       0x000001686c8312d0ULL, 0x000002472d96a909ULL,
-- >       0x000003af9a19bbd9ULL, 0x000005f6c7b064e2ULL, 0x000009a661ca20bbULL
-- >   };
-- >   const SWord64 s65 = s0 >= 65 ? 0x0000000000000000ULL : table0[s0];
-- >   
-- >   return s65;
-- > }
genFib2 :: SWord64 -> IO ()
genFib2 top = compileToC Nothing "fibLookup" $ do
        cgPerformRTCs True       -- protect against potential overflow, our table is not big enough
        x <- cgInput "x"
        cgReturn $ fib2 top x
