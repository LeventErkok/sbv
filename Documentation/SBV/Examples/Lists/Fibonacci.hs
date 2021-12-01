-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Lists.Fibonacci
-- Copyright : (c) Joel Burget
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Define the fibonacci sequence as an SBV symbolic list.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Lists.Fibonacci where

import Data.SBV

import Prelude hiding ((!!))

import           Data.SBV.List ((!!))
import qualified Data.SBV.List as L

import Data.SBV.Control

-- | Compute a prefix of the fibonacci numbers. We have:
--
-- >>> mkFibs 10
-- [1,1,2,3,5,8,13,21,34,55]
mkFibs :: Int -> IO [Integer]
mkFibs n = take n <$> runSMT genFibs

-- | Generate fibonacci numbers as a sequence. Note that we constrain only
-- the first 200 entries.
genFibs :: Symbolic [Integer]
genFibs = do fibs <- sList "fibs"

             -- constrain the length
             constrain $ L.length fibs .== 200

             -- Constrain first two elements
             constrain $ fibs !! 0 .== 1
             constrain $ fibs !! 1 .== 1

             -- Constrain an arbitrary element at index `i`
             let constr i = constrain $ fibs !! i + fibs !! (i+1) .== fibs !! (i+2)

             -- Constrain the remaining elts
             mapM_ (constr . fromIntegral) [(0::Int) .. 197]

             query $ do cs <- checkSat
                        case cs of
                          Unk    -> error "Solver returned unknown!"
                          DSat{} -> error "Unexpected dsat result!"
                          Unsat  -> error "Solver couldn't generate the fibonacci sequence!"
                          Sat    -> getValue fibs
