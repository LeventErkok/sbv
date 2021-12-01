-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.Tuple
-- Copyright : (c) Joel Burget
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A basic tuple use case, also demonstrating regular expressions,
-- strings, etc. This is a basic template for getting SBV to produce
-- valid data for applications that require inputs that satisfy
-- arbitrary criteria.
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Misc.Tuple where

import Data.SBV
import Data.SBV.Tuple
import Data.SBV.Control

import Prelude hiding ((!!))
import Data.SBV.List   ((!!))
import Data.SBV.RegExp

import qualified Data.SBV.String as S
import qualified Data.SBV.List   as L

-- | A dictionary is a list of lookup values. Note that we
-- store the type @[(a, b)]@ as a symbolic value here, mixing
-- sequences and tuples.
type Dict a b = SBV [(a, b)]

-- | Create a dictionary of length 5, such that each element
-- has an string key and each value is the length of the key.
-- We impose a few more constraints to make the output interesting. 
-- For instance, you might get:
--
-- @ ghci> example
-- [("nt_",3),("dHAk",4),("kzkk0",5),("mZxs9s",6),("c32'dPM",7)]
-- @
--
-- Depending on your version of z3, a different answer might be provided.
-- Here, we check that it satisfies our length conditions:
--
-- >>> import Data.List (genericLength)
-- >>> example >>= \ex -> return (length ex == 5 && all (\(l, i) -> genericLength l == i) ex)
-- True
example :: IO [(String, Integer)]
example = runSMT $ do dict :: Dict String Integer <- free "dict"

                      -- require precisely 5 elements
                      let len   = 5 :: Int
                          range = [0 .. len - 1]

                      constrain $ L.length dict .== fromIntegral len

                      -- require each key to be at of length 3 more than the index it occupies
                      -- and look like an identifier
                      let goodKey i s = let l = S.length s
                                            r = asciiLower * KStar (asciiLetter + digit + "_" + "'")
                                      in l .== fromIntegral i+3 .&& s `match` r

                          restrict i = case untuple (dict !! fromIntegral i) of
                                         (k, v) -> constrain $ goodKey i k .&& v .== S.length k

                      mapM_ restrict range

                      -- require distinct keys:
                      let keys = [(dict !! fromIntegral i)^._1 | i <- range]
                      constrain $ distinct keys

                      query $ do ensureSat
                                 getValue dict
