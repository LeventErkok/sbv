-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.CodeGeneration.AddSub.hs
-- Copyright   :  (c) Lee Pike
-- License     :  BSD3
-- Maintainer  :  leepike@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Code generation example that generates the Fibonacci sequence.  
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Examples.CodeGeneration.Fib where

import Data.SBV

fib :: SWord8 -> SWord8 -> SWord8
fib top n = fib' (0,1,0)
  where fib' :: (SWord8,SWord8,SWord8) -> SWord8
        fib' (acc2,acc1,m) = 
          if m == top then acc2
            else fib' ( ite (n .> m) acc1 acc2
                      , ite (n .> m) (acc1 + acc2) acc1
                      , m+1)

-- | Generates C code that implements the Fibonacci sequence.  The generated
-- program takes a single argument that is the index into the sequence to be
-- returned.  Note that we have to give an upper-bound on the number of elements
-- to generate, as the code generator only generates straight-line code.
gen :: SWord8 -> IO ()  
gen top = compileToC True (Just "mytest") "mytest" [] (\(x::SWord8) -> fib top x)
