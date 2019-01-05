-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.Birthday
-- Author    : Levent Erkok
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
-- Albert and Bernard just met Cheryl. “When’s your birthday?” Albert asked Cheryl.
--
-- Cheryl thought a second and said, “I’m not going to tell you, but I’ll give you some clues.” She wrote down a list of 10 dates:
--
--   May 15, May 16, May 19
--   June 17, June 18
--   July 14, July 16
--   August 14, August 15, August 17
--
-- “My birthday is one of these,” she said.
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

module Documentation.SBV.Examples.Puzzles.Birthday where

import Data.SBV

-----------------------------------------------------------------------------------------------
-- * Types and values
-----------------------------------------------------------------------------------------------

-- | Represent month by 8-bit words; We can also use an uninterpreted type, but numbers work well here.
type Month = SWord8

-- | Represent day by 8-bit words; Again, an uninterpreted type would work as well.
type Day = SWord8

-- | Months referenced in the problem.
may, june, july, august :: SWord8
[may, june, july, august] = [5, 6, 7, 8]

-----------------------------------------------------------------------------------------------
-- * Helper predicates
-----------------------------------------------------------------------------------------------

-- | Check that a given month/day combo is a possible birth-date.
valid :: Month -> Day -> SBool
valid month day = (month, day) `sElem` candidates
  where candidates :: [(Month, Day)]
        candidates = [ (   may, 15), (   may, 16), (   may, 19)
                     , (  june, 17), (  june, 18)
                     , (  july, 14), (  july, 16)
                     , (august, 14), (august, 15), (august, 17)
                     ]

-- | Assert that the given function holds for one of the possible days.
existsDay :: (Day -> SBool) -> SBool
existsDay f = sAny (f . literal) [14 .. 19]

-- | Assert that the given function holds for all of the possible days.
forallDay :: (Day -> SBool) -> SBool
forallDay f = sAll (f . literal) [14 .. 19]

-- | Assert that the given function holds for one of the possible months.
existsMonth :: (Month -> SBool) -> SBool
existsMonth f = sAny f [may .. august]

-- | Assert that the given function holds for all of the possible months.
forallMonth :: (Month -> SBool) -> SBool
forallMonth f = sAll f [may .. august]

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
puzzle :: Predicate
puzzle = do birthDay   <- exists "birthDay"
            birthMonth <- exists "birthMonth"

            -- Albert: I do not know
            let a1 m = existsDay $ \d1 -> existsDay $ \d2 ->
                           d1 ./= d2 .&& valid m d1 .&& valid m d2

            -- Albert: I know that Bernard doesn't know
            let a2 m = forallDay $ \d -> valid m d .=>
                          existsMonth (\m1 -> existsMonth $ \m2 ->
                                m1 ./= m2 .&& valid m1 d .&& valid m2 d)

            -- Bernard: I did not know
            let b1 d = existsMonth $ \m1 -> existsMonth $ \m2 ->
                           m1 ./= m2 .&& valid m1 d .&& valid m2 d

            -- Bernard: But now I know
            let b2p m d = valid m d .&& a1 m .&& a2 m
                b2  d   = forallMonth $ \m1 -> forallMonth $ \m2 ->
                                (b2p m1 d .&& b2p m2 d) .=> m1 .== m2

            -- Albert: Now I know too
            let a3p m d = valid m d .&& a1 m .&& a2 m .&& b1 d .&& b2 d
                a3 m    = forallDay $ \d1 -> forallDay $ \d2 ->
                                (a3p m d1 .&& a3p m d2) .=> d1 .== d2

            -- Assert all the statements made:
            constrain $ a1 birthMonth
            constrain $ a2 birthMonth
            constrain $ b1 birthDay
            constrain $ b2 birthDay
            constrain $ a3 birthMonth

            -- Find a valid birth-day that satisfies the above constraints:
            return $ valid birthMonth birthDay

-- | Find all solutions to the birthday problem. We have:
--
-- >>> cheryl
-- Solution #1:
--   birthDay   = 16 :: Word8
--   birthMonth =  7 :: Word8
-- This is the only solution.
cheryl :: IO ()
cheryl = print =<< allSat puzzle
