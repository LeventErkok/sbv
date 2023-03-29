-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Optimization.VM
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Solves a VM allocation problem using optimization features
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Optimization.VM where

import Data.SBV

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV

-- | Computer allocation problem:
--
--   - We have three virtual machines (VMs) which require 100, 50 and 15 GB hard disk respectively.
--
--   - There are three servers with capabilities 100, 75 and 200 GB in that order.
--
--   - Find out a way to place VMs into servers in order to
--
--        - Minimize the number of servers used
--
--        - Minimize the operation cost (the servers have fixed daily costs 10, 5 and 20 USD respectively.)
--
-- We have:
--
-- >>> optimize Lexicographic allocate
-- Optimal model:
--   x11         = False :: Bool
--   x12         = False :: Bool
--   x13         =  True :: Bool
--   x21         = False :: Bool
--   x22         = False :: Bool
--   x23         =  True :: Bool
--   x31         = False :: Bool
--   x32         = False :: Bool
--   x33         =  True :: Bool
--   noOfServers =     1 :: Integer
--   cost        =    20 :: Integer
--
-- That is, we should put all the jobs on the third server, for a total cost of 20.
allocate :: ConstraintSet
allocate = do
    -- xij means VM i is running on server j
    x1@[x11, x12, x13] <- sBools ["x11", "x12", "x13"]
    x2@[x21, x22, x23] <- sBools ["x21", "x22", "x23"]
    x3@[x31, x32, x33] <- sBools ["x31", "x32", "x33"]

    -- Each job runs on exactly one server
    constrain $ pbStronglyMutexed x1
    constrain $ pbStronglyMutexed x2
    constrain $ pbStronglyMutexed x3

    let need :: [SBool] -> SInteger
        need rs = sum $ zipWith (\r c -> ite r c 0) rs [100, 50, 15]

    -- The capacity on each server is respected
    let capacity1 = need [x11, x21, x31]
        capacity2 = need [x12, x22, x32]
        capacity3 = need [x13, x23, x33]

    constrain $ capacity1 .<= 100
    constrain $ capacity2 .<=  75
    constrain $ capacity3 .<= 200

    -- compute #of servers running:
    let y1 = sOr [x11, x21, x31]
        y2 = sOr [x12, x22, x32]
        y3 = sOr [x13, x23, x33]

        b2n b = ite b 1 0

    let noOfServers = sum $ map b2n [y1, y2, y3]

    -- minimize # of servers
    minimize "noOfServers" (noOfServers :: SInteger)

    -- cost on each server
    let cost1 = ite y1 10 0
        cost2 = ite y2  5 0
        cost3 = ite y3 20 0

    -- minimize the total cost
    minimize "cost" (cost1 + cost2 + cost3 :: SInteger)
