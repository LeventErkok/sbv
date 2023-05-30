-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.Birthday
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- This is a formalization of the Cheryl's birthday problem, which went viral in April 2015.
-- (See <http://www.nytimes.com/2015/04/15/science/a-math-problem-from-singapore-goes-viral-when-is-cheryls-birthday.html>.)
--
-- Here's the puzzle:
--
-- @
-- Albert and Bernard just met Cheryl. "When’s your birthday?" Albert asked Cheryl.
--
-- Cheryl thought a second and said, "I’m not going to tell you, but I’ll give you some clues." She wrote down a list of 10 dates:
--
--   May 15, May 16, May 19
--   June 17, June 18
--   July 14, July 16
--   August 14, August 15, August 17
--
-- "My birthday is one of these," she said.
--
-- Then Cheryl whispered in Albert’s ear the month — and only the month — of her birthday. To Bernard, she whispered the day, and only the day. 
-- “Can you figure it out now?” she asked Albert.
--
-- Albert: I don’t know when your birthday is, but I know Bernard doesn’t know, either.
-- Bernard: I didn’t know originally, but now I do.
-- Albert: Well, now I know, too!
--
-- When is Cheryl’s birthday?
-- @
--
-- NB. Thanks to Amit Goel for suggesting the formalization strategy used in here.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.Birthday where

import Data.SBV

-----------------------------------------------------------------------------------------------
-- * Types and values
-----------------------------------------------------------------------------------------------

-- | Months. We only put in the months involved in the puzzle for simplicity
data Month = May | Jun | Jul | Aug

-- | Days. Again, only the ones mentioned in the puzzle.
data Day = D14 | D15 | D16 | D17 | D18 | D19

mkSymbolicEnumeration ''Month
mkSymbolicEnumeration ''Day

-- | Represent the birthday as a record
data Birthday = BD SMonth SDay

-- | Make a valid symbolic birthday
mkBirthday :: Symbolic Birthday
mkBirthday = do b <- BD <$> free "birthMonth" <*> free "birthDay"
                constrain $ valid b
                pure b

-- | Is this a valid birthday? i.e., one that was declared by Cheryl to be a possibility.
valid :: Birthday -> SBool
valid (BD m d) =   (m .== sMay .=> d `sElem` [sD15, sD16, sD19])
               .&& (m .== sJun .=> d `sElem` [sD17, sD18])
               .&& (m .== sJul .=> d `sElem` [sD14, sD16])
               .&& (m .== sAug .=> d `sElem` [sD14, sD15, sD17])

-----------------------------------------------------------------------------------------------
-- * The puzzle
-----------------------------------------------------------------------------------------------

-- | Encode the conversation as given in the puzzle.
--
-- NB. Lee Pike pointed out that not all the constraints are actually necessary! (Private
-- communication.) The puzzle still has a unique solution if the statements @a1@ and @b1@
-- (i.e., Albert and Bernard saying they themselves do not know the answer) are removed.
-- To experiment you can simply comment out those statements and observe that there still
-- is a unique solution. Thanks to Lee for pointing this out! In fact, it is instructive to
-- assert the conversation line-by-line, and see how the search-space gets reduced in each
-- step.
puzzle :: ConstraintSet
puzzle = do BD birthMonth birthDay <- mkBirthday

            let ok    = sAll valid
                qe qb = quantifiedBool qb

            -- Albert: I do not know
            let a1 m = qe $ \(Exists d1) (Exists d2) -> ok [BD m d1, BD m d2] .&& d1 ./= d2
            constrain $ a1 birthMonth

            -- Albert: I know that Bernard doesn't know
            let a2 m = qe $ \(Forall d) -> ok [BD m d] .=> qe (\(Exists m1) (Exists m2) -> ok [BD m1 d, BD m2 d] .&& m1 ./= m2)
            constrain $ a2 birthMonth

            -- Bernard: I did not know
            let b1 d = qe $ \(Exists m1) (Exists m2) -> ok [BD m1 d, BD m2 d] .&& m1 ./= m2
            constrain $ b1 birthDay

            -- Bernard: But now I know
            let b2p m d = ok [BD m d] .&& a1 m .&& a2 m
                b2  d   = qe $ \(Forall m1) (Forall m2) -> (b2p m1 d .&& b2p m2 d) .=> m1 .== m2
            constrain $ b2 birthDay

            -- Albert: Now I know too
            let a3p m d = ok [BD m d] .&& a1 m .&& a2 m .&& b1 d .&& b2 d
                a3  m   = \(Forall d1) (Forall d2) -> (a3p m d1 .&& a3p m d2) .=> d1 .== d2
            constrain $ a3 birthMonth

-- | Find all solutions to the birthday problem. We have:
--
-- >>> cheryl
-- Solution #1:
--   birthMonth = Jul :: Month
--   birthDay   = D16 :: Day
-- This is the only solution.
cheryl :: IO ()
cheryl = print =<< allSat puzzle

{- HLint ignore puzzle "Redundant lambda" -}
{- HLint ignore puzzle "Eta reduce"       -}
