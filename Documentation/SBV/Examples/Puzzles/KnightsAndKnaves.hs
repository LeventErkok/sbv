-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.KnightsAndKnaves
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- From Raymond Smullyan: On a fictional island, all inhabitants are either knights,
-- who always tell the truth, or knaves, who always lie. John and Bill are residents
-- of the island of knights and knaves. John and Bill make several utterances.
-- Determine which one is a knave or a knight, depending on their answers.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

module Documentation.SBV.Examples.Puzzles.KnightsAndKnaves where

import Prelude hiding (and, not)

import Data.SBV
import Data.SBV.Control

-- | Inhabitants of the island, as an uninterpreted sort
data Inhabitant
mkUninterpretedSort ''Inhabitant

-- | Each inhabitant is either a knave or a knight
data Identity = Knave | Knight
mkSymbolicEnumeration ''Identity

-- | Statements are utterances which are either true or false
data Statement = Truth | Falsity
mkSymbolicEnumeration ''Statement

-- | John is an inhabitant of the island.
john :: SInhabitant
john = uninterpret "John"

-- | Bill is an inhabitant of the island.
bill :: SInhabitant
bill = uninterpret "Bill"

-- | The connective 'is' makes a statement about an inhabitant regarding his/her identity.
is :: SInhabitant -> SIdentity -> SStatement
is = uninterpret "is"

-- | The connective 'says' makes a predicate from what an inhabitant states
says :: SInhabitant -> SStatement -> SBool
says = uninterpret "says"

-- | The connective 'holds' is will be true if the statement is true
holds :: SStatement -> SBool
holds = uninterpret "holds"

-- | The connective 'and' creates the conjunction of two statements
and :: SStatement -> SStatement -> SStatement
and = uninterpret "AND"

-- | The connective 'not' negates a statement
not :: SStatement -> SStatement
not = uninterpret "NOT"

-- | The connective 'iff' creates a statement that equates the truth values of its argument statements
iff :: SStatement -> SStatement -> SStatement
iff = uninterpret "IFF"

-- | Encode Smullyan's puzzle. We have:
--
-- >>> puzzle
-- Question 1.
--   John says, We are both knaves
--     Then, John is: Knave
--     And,  Bill is: Knight
-- Question 2.
--   John says If (and only if) Bill is a knave, then I am a knave.
--   Bill says We are of different kinds.
--     Then, John is: Knave
--     And,  Bill is: Knight
puzzle :: IO ()
puzzle = runSMT $ do

    -- truth holds, falsity doesn't
    constrain $ holds sTruth
    constrain $ sNot $ holds sFalsity

    -- Each inhabitant is either a knave or a knight
    constrain $ \(Forall x) -> holds (is x sKnave) .<+> holds (is x sKnight)

    -- If x is a knave and he says something, then that statement is false
    constrain $ \(Forall x) (Forall y) -> holds (is x sKnave)  .=> (says x y .=> sNot (holds y))

    -- If x is a knight and he says something, then that statement is true
    constrain $ \(Forall x) (Forall y) -> holds (is x sKnight) .=> (says x y .=> holds y)

    -- The meaning of conjunction: It holds whenever both statements hold
    constrain $ \(Forall x) (Forall y) -> holds (and x y) .== (holds x .&& holds y)

    -- The meaning of negation: It holds when the original doesn't
    constrain $ \(Forall x) -> holds (not x) .== sNot (holds x)

    -- The meaning of iff: both statements hold or don't hold at the same time
    constrain $ \(Forall x) (Forall y) -> holds (iff x y) .== (holds x .== holds y)

    query $ do

      -- helper to get the responses out
      let checkStatus = do cs <- checkSat
                           case cs of
                             Sat -> do jk <- getValue (holds (is john sKnight))
                                       bk <- getValue (holds (is bill sKnight))
                                       io $ putStrLn $ "    Then, John is: " ++ if jk then "Knight" else "Knave"
                                       io $ putStrLn $ "    And,  Bill is: " ++ if bk then "Knight" else "Knave"
                             _   -> error $ "Solver said: " ++ show cs

          question w q = inNewAssertionStack $ do
                io $ putStrLn w
                q >> checkStatus

      -- Question 1
      question "Question 1." $ do
         io $ putStrLn "  John says, We are both knaves"
         constrain $ says john (and (is john sKnave) (is bill sKnave))

      -- Question 2
      question "Question 2." $ do
         io $ putStrLn "  John says If (and only if) Bill is a knave, then I am a knave."
         io $ putStrLn "  Bill says We are of different kinds."
         constrain $ says john (iff (is bill sKnave) (is john sKnave))
         constrain $ says bill (not (iff (is bill sKnave) (is john sKnave)))
