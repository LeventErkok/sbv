-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.GenTest
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test generation from symbolic programs
-----------------------------------------------------------------------------

module Data.SBV.BitVectors.GenTest (genTest) where

import Data.Maybe (fromMaybe)

import Data.SBV.BitVectors.Data

-- | Generate a set of concrete test values from a symbolic program. The output
-- can be rendered as test vectors in different languages as necessary. Use the
-- function 'output' call to indicate what fields should be in the test result.
genTest :: Int -> Symbolic () -> IO [([CW], [CW])]
genTest n m = sequence [tc | _ <- [1 .. n]]
  where tc = do (_, Result _ tvals _ _ cs _ _ _ _ _ cstrs os) <- runSymbolic' Concrete m
                case cstrs of
                  [] -> let cval = fromMaybe (error "Cannot quick-check in the presence of uninterpeted constants!") . (`lookup` cs)
                        in return (map snd tvals, map cval os)
                  _  -> error "Not yet supported: Quickcheck in the presence of explicit constraints."
