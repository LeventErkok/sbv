-----------------------------------------------------------------------------
-- |
-- Module      :  Documentation.SBV.Examples.Sequences.Fibonacci
-- Copyright   :  (c) Joel Burget
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Define the fibonacci sequence as an SBV sequence.
-----------------------------------------------------------------------------

module Documentation.SBV.Examples.Sequences.Fibonacci where

import Prelude hiding (length)
import Data.Traversable (for)

import Data.SBV
import Data.SBV.Sequence
import Data.SBV.Control

-- | How many elements to produce
seqLength :: Integer
seqLength = 200

-- | Print a prefix of the fibonacci sequence.
main :: IO ()
main = do
  fibs <- runSMTWith z3 $ do
    fibs <- sSequence "fibs"

    constrain $ fibs .!! 0 .== 1
    constrain $ fibs .!! 1 .== 1

    _ <- for (fromIntegral <$> [0..seqLength - 3]) $ \ix ->
      constrain $ fibs .!! (ix + 0)
                + fibs .!! (ix + 1)
              .== fibs .!! (ix + 2)
    constrain $ length fibs .== fromIntegral seqLength

    query $ do cs <- checkSat
               case cs of
                 Unk   -> error "Solver returned unknown!"
                 Unsat -> error "No example found"
                 Sat   -> getValue fibs
  print (fibs :: Sequence Integer)
