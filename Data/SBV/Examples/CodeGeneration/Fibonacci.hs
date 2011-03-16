-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.CodeGeneration.Fibonacci
-- Copyright   :  (c) Lee Pike, Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Computing Fibonacci numbers and generating C code. Inspired by Lee Pike's
-- original implementation, modified for inclusion in the package. It illustrates
-- symbolic termination issues one can have when working with recursive algorithms
-- and how to deal with such, eventually generating good C code.
-----------------------------------------------------------------------------

module Data.SBV.Examples.CodeGeneration.Fibonacci where

import Data.SBV

-----------------------------------------------------------------------------
-- * A naive implementation
-----------------------------------------------------------------------------

-- | This is a naive implementation of fibonacci, and will work fine (albeit slow)
-- for concrete inputs:
--
-- >>> map fib0 [0..6]
-- [0 :: SWord32,1 :: SWord32,1 :: SWord32,2 :: SWord32,3 :: SWord32,5 :: SWord32,8 :: SWord32]
--
-- However, it is not suitable for doing proofs or generating code, as it is not
-- symbolically terminating when it is called with a symbolic value @n@. When we
-- recursively call @fib0@ on @n-1@ (or @n-2@), the test against @0@ will always
-- explore both branches since the result will be symbolic, hence will not
-- terminate. (An integrated theorem prover can establish termination
-- after a certain number of unrollings, but this would be quite expensive to
-- implement, and would be impractical.)
fib0 :: SWord32 -> SWord32
fib0 n = ite (n .== 0 ||| n .== 1)
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
-- [0 :: SWord32,1 :: SWord32,1 :: SWord32,2 :: SWord32,3 :: SWord32,5 :: SWord32,8 :: SWord32]
--
-- The function will work correctly, so long as the index we query is at most @top@, and otherwise
-- will return the value at @top@. Note that we also use accumulating parameters here for efficiency,
-- although this is orthogonal to the termination concern.
fib1 :: SWord32 -> SWord32 -> SWord32
fib1 top n = fib' 0 1 0
  where fib' :: SWord32 -> SWord32 -> SWord32 -> SWord32
        fib' prev' prev m = ite (m .== top ||| m .== n)          -- did we reach recursion depth, or the index we're looking for
                                prev'                            -- stop and return the result
                                (fib' prev (prev' + prev) (m+1)) -- otherwise recurse

-- | We can generate code for 'fib1' using the 'genFib1' action. Note that the
-- generated code will grow larger as we pick larger values of @top@, but only linearly,
-- thanks to the accumulating parameter trick used by 'fib1'. The following is an excerpt
-- from the code generated for the call @genFib1 10@, where the code will work correctly
-- for indexes up to 10:
--
-- > SWord32 fib1(const SWord32 s0)
-- > {
-- >   const SBool   s2 = s0 == 0x00000000UL;
-- >   const SBool   s4 = s0 == 0x00000001UL;
-- >   const SBool   s6 = s0 == 0x00000002UL;
-- >   const SBool   s8 = s0 == 0x00000003UL;
-- >   const SBool   s10 = s0 == 0x00000004UL;
-- >   const SBool   s12 = s0 == 0x00000005UL;
-- >   const SBool   s14 = s0 == 0x00000006UL;
-- >   const SBool   s17 = s0 == 0x00000007UL;
-- >   const SBool   s19 = s0 == 0x00000008UL;
-- >   const SBool   s22 = s0 == 0x00000009UL;
-- >   const SWord32 s25 = s22 ? 0x00000022UL : 0x00000037UL;
-- >   const SWord32 s26 = s19 ? 0x00000015UL : s25;
-- >   const SWord32 s27 = s17 ? 0x0000000dUL : s26;
-- >   const SWord32 s28 = s14 ? 0x00000008UL : s27;
-- >   const SWord32 s29 = s12 ? 0x00000005UL : s28;
-- >   const SWord32 s30 = s10 ? 0x00000003UL : s29;
-- >   const SWord32 s31 = s8 ? 0x00000002UL : s30;
-- >   const SWord32 s32 = s6 ? 0x00000001UL : s31;
-- >   const SWord32 s33 = s4 ? 0x00000001UL : s32;
-- >   const SWord32 s34 = s2 ? 0x00000000UL : s33;
-- >   
-- >   return s34;
-- > }
genFib1 :: SWord32 -> IO ()  
genFib1 top = compileToC False Nothing "fib1" [] (fib1 top)

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
fib2 :: SWord32 -> SWord32 -> SWord32
fib2 top n = select table 0 n
  where table = map (fib1 top) [0 .. top]

-- | Once we have 'fib2', we can generate the C code straightforwardly. Below
-- is an excerpt from the code that SBV generates for the call @genFib2 64@. Note
-- that this code is a constant-time look-up table implementation of fibonacci,
-- with no run-time overhead. The index can be made arbitrarily large,
-- naturally. (Note that this function returns @0@ if the index is larger
-- than 64, as specified by the call to 'select' with default @0@.)
--
-- > SWord32 fibLookup(const SWord32 s0)
-- > {
-- >   static const SWord32 table0[] = {
-- >       0x00000000UL, 0x00000001UL, 0x00000001UL, 0x00000002UL,
-- >       0x00000003UL, 0x00000005UL, 0x00000008UL, 0x0000000dUL,
-- >       0x00000015UL, 0x00000022UL, 0x00000037UL, 0x00000059UL,
-- >       0x00000090UL, 0x000000e9UL, 0x00000179UL, 0x00000262UL,
-- >       0x000003dbUL, 0x0000063dUL, 0x00000a18UL, 0x00001055UL,
-- >       0x00001a6dUL, 0x00002ac2UL, 0x0000452fUL, 0x00006ff1UL,
-- >       0x0000b520UL, 0x00012511UL, 0x0001da31UL, 0x0002ff42UL,
-- >       0x0004d973UL, 0x0007d8b5UL, 0x000cb228UL, 0x00148addUL,
-- >       0x00213d05UL, 0x0035c7e2UL, 0x005704e7UL, 0x008cccc9UL,
-- >       0x00e3d1b0UL, 0x01709e79UL, 0x02547029UL, 0x03c50ea2UL,
-- >       0x06197ecbUL, 0x09de8d6dUL, 0x0ff80c38UL, 0x19d699a5UL,
-- >       0x29cea5ddUL, 0x43a53f82UL, 0x6d73e55fUL, 0xb11924e1UL,
-- >       0x1e8d0a40UL, 0xcfa62f21UL, 0xee333961UL, 0xbdd96882UL,
-- >       0xac0ca1e3UL, 0x69e60a65UL, 0x15f2ac48UL, 0x7fd8b6adUL,
-- >       0x95cb62f5UL, 0x15a419a2UL, 0xab6f7c97UL, 0xc1139639UL,
-- >       0x6c8312d0UL, 0x2d96a909UL, 0x9a19bbd9UL, 0xc7b064e2UL,
-- >       0x61ca20bbUL
-- >   };
-- >   const SWord32 s65 = s0 >= 65 ? 0x00000000UL : table0[s0];
-- >   
-- >   return s65;
-- > }
genFib2 :: SWord32 -> IO ()
genFib2 top = compileToC True Nothing "fibLookup" [] (fib2 top)
