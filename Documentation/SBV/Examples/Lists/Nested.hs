-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Lists.Nested
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates nested lists
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Documentation.SBV.Examples.Lists.Nested where

import Data.SBV
import Data.SBV.Control

import Data.SBV.List ((.!!))
import qualified Data.SBV.List as L

-- | Simple example demonstrating the use of nested lists. We have:
--
-- >>> nestedExample
-- [[1,2,3],[4,5,6,7],[8,9,10],[11,12,13]]
nestedExample :: IO ()
nestedExample = runSMT $ do a :: SList [Integer] <- free "a"

                            constrain $ a .!! 0 .== [1, 2, 3]
                            constrain $ a .!! 1 .== [4, 5, 6, 7]
                            constrain $ L.tail (L.tail a) .== [[8, 9, 10], [11, 12, 13]]
                            constrain $ L.length a .== 4

                            query $ do cs <- checkSat
                                       case cs of
                                         Unk   -> error "Solver said unknown!"
                                         Unsat -> io $ putStrLn "Unsat"
                                         Sat   -> do v <- getValue a
                                                     io $ print v
