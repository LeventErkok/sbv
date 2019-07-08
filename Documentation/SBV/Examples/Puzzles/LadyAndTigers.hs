-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.LadyAndTigers
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Puzzle:
--
--    You are standing in front of three rooms and must choose one. In one room is a Lady
--    (whom you could and wish to marry), in the other two rooms are tigers (that if you
--    choose either of these rooms, the tiger invites you to breakfast – the problem is
--    that you are the main course). Your job is to choose the room with the Lady.
--    The signs on the doors are:
--
--         * A Tiger is in this room
--         * A Lady is in this room
--         * A Tiger is in room two
--
--    At most only 1 statement is true. Where’s the Lady?
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.LadyAndTigers where

import Data.SBV

-- | Prints the only solution:
--
-- >>> ladyAndTigers
-- Solution #1:
--   sign1  = False :: Bool
--   sign2  = False :: Bool
--   sign3  =  True :: Bool
--   tiger1 = False :: Bool
--   tiger2 =  True :: Bool
--   tiger3 =  True :: Bool
-- This is the only solution.
--
-- That is, the lady is in room 1, and only the third room's sign is true.
ladyAndTigers :: IO AllSatResult
ladyAndTigers = allSat $ do

    -- One boolean for each of the correctness of the signs
    [sign1, sign2, sign3] <- mapM sBool ["sign1", "sign2", "sign3"]

    -- One boolean for each of the presence of the tigers
    [tiger1, tiger2, tiger3] <- mapM sBool ["tiger1", "tiger2", "tiger3"]

    -- Room 1 sign: A Tiger is in this room
    constrain $ sign1 .<=> tiger1

    -- Room 2 sign: A Lady is in this room
    constrain $ sign2 .<=> sNot tiger2

    -- Room 3 sign: A Tiger is in room 2
    constrain $ sign3 .<=> tiger2

    -- At most one sign is true
    constrain $ [sign1, sign2, sign3] `pbAtMost` 1

    -- There are precisely two tigers
    constrain $ [tiger1, tiger2, tiger3] `pbExactly` 2
