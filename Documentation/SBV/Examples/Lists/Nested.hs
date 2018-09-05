-----------------------------------------------------------------------------
-- |
-- Module      :  Documentation.SBV.Examples.Lists.Nested
-- Copyright   :  (c) Joel Burget
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
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

import GHC.Exts(IsList(toList))

-- | Simple example demonstrating the use of nested lists. We have:
--
-- >>> nestedExample
-- [[1,2,3],[4,5,6,7]]
nestedExample :: IO ()
nestedExample = runSMT $ do a :: SList (List Integer) <- free "a"

                            constrain $ a .!! 0 .== [1, 2, 3]
                            constrain $ a .!! 1 .== [4, 5, 6, 7]
                            constrain $ L.length a .== 2

                            query $ do cs <- checkSat
                                       case cs of
                                         Unk   -> error "Solver said unknown!"
                                         Unsat -> io $ putStrLn "Unsat"
                                         Sat   -> do v <- (map toList . toList) <$> getValue a
                                                     io $ print (v :: [[Integer]])
