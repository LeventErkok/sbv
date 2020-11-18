-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.Murder
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Solution to "Malice and Alice," from George J. Summers' Logical Deduction Puzzles:
--
-- @
-- A man and a woman were together in a bar at the time of the murder.
-- The victim and the killer were together on a beach at the time of the murder.
-- One of Alice’s two children was alone at the time of the murder.
-- Alice and her husband were not together at the time of the murder.
-- The victim's twin was not the killer.
-- The killer was younger than the victim.
--
-- Who killed who?
-- @
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# OPTIONS_GHC -Wall -Werror   #-}

module Documentation.SBV.Examples.Puzzles.Murder where

import Data.Char
import Data.List

import Data.SBV
import Data.SBV.Control

-- | Locations
data Location = Bar | Beach | Alone

-- | Sexes
data Sex  = Male | Female

-- | Roles
data Role = Victim | Killer | Bystander

mkSymbolicEnumeration ''Location
mkSymbolicEnumeration ''Sex
mkSymbolicEnumeration ''Role

-- | A person has a name, age, together with location and sex.
-- We parameterize over a function so we can use this struct
-- both in a concrete context and a symbolic context. Note
-- that the name is always concrete.
data Person f = Person { nm       :: String
                       , age      :: f Integer
                       , location :: f Location
                       , sex      :: f Sex
                       , role     :: f Role
                       }

-- | Helper functor
newtype Const a = Const { getConst :: a }

-- | Show a person
instance Show (Person Const) where
  show (Person n a l s r) = unwords [n, show (getConst a), show (getConst l), show (getConst s), show (getConst r)]

-- | Create a new symbolic person
newPerson :: String -> Symbolic (Person SBV)
newPerson n = do
        p <- Person n <$> free_ <*> free_ <*> free_ <*> free_
        constrain $ age p .>= 20
        constrain $ age p .<= 50
        pure p

-- | Get the concrete value of the person in the model
getPerson :: Person SBV -> Query (Person Const)
getPerson Person{nm, age, location, sex, role} = Person nm <$> (Const <$> getValue age)
                                                           <*> (Const <$> getValue location)
                                                           <*> (Const <$> getValue sex)
                                                           <*> (Const <$> getValue role)

-- | Solve the puzzle. We have:
--
-- >>> killer
-- alice     47  Bar    Female  Bystander
-- husband   46  Beach  Male    Killer
-- brother   47  Beach  Male    Victim
-- daughter  20  Alone  Female  Bystander
-- son       20  Bar    Male    Bystander
--
-- That is, Alice's brother was the victim and Alice's husband was the killer.
killer :: IO ()
killer = do
   persons <- puzzle
   let wps      = map (words . show) persons
       cwidths  = map ((+2) . maximum . map length) (transpose wps)
       align xs = concat $ zipWith (\i f -> take i (f ++ repeat ' ')) cwidths xs
       trim     = reverse . dropWhile isSpace . reverse
   mapM_ putStrLn $ map (trim . align) wps

-- | Constraints of the puzzle, coded following the English description.
puzzle :: IO [Person Const]
puzzle = runSMT $ do
  alice    <- newPerson "alice"
  husband  <- newPerson "husband"
  brother  <- newPerson "brother"
  daughter <- newPerson "daughter"
  son      <- newPerson "son"

  -- Sex of each character
  constrain $ sex alice    .== sFemale
  constrain $ sex husband  .== sMale
  constrain $ sex brother  .== sMale
  constrain $ sex daughter .== sFemale
  constrain $ sex son      .== sMale

  let chars = [alice, husband, brother, daughter, son]

  -- Age relationships
  constrain $ age son .== age daughter .|| age alice .== age brother
  constrain $ age son      .<  age alice    - 25
  constrain $ age son      .<  age husband  - 25
  constrain $ age daughter .<  age alice    - 25
  constrain $ age daughter .<  age husband  - 25

  -- One victim, one killer
  constrain $ sum (map (\c -> oneIf (role c .== sVictim)) chars) .== (1 :: SInteger)
  constrain $ sum (map (\c -> oneIf (role c .== sKiller)) chars) .== (1 :: SInteger)

  -- A man and a woman were together in a bar at the time of the murder.
  constrain $ sOr (map (\c -> sex c .== sFemale .&& location c .== sBar)  chars)
  constrain $ sOr (map (\c -> sex c .== sMale   .&& location c .== sBar)  chars)

  let ifVictim p = role p .== sVictim
      ifKiller p = role p .== sKiller

      every f = sAnd (map f chars)
      some  f = sOr  (map f chars)

  -- The victim and the killer were together on a beach at the time of the murder.
  constrain $ every $ \c -> ifVictim c .=> location c .== sBeach
  constrain $ every $ \c -> ifKiller c .=> location c .== sBeach

  -- One of Alice’s two children was alone at the time of the murder.
  constrain $ location daughter .== sAlone .|| location son .== sAlone

  -- Alice and her husband were not together at the time of the murder.
  constrain $ location alice ./= location husband

  -- The victim has a twin
  constrain $ every $ \c -> ifVictim c .=> some (\d -> literal (nm c /= nm d) .&& age c .== age d)

  -- The victim's twin was not the killer.
  constrain $ every $ \c -> ifVictim c .=> every (\d -> age c .== age d .=> role d ./= sKiller)

  -- The killer was younger than the victim.
  constrain $ every $ \c -> ifKiller c .=> every (\d -> ifVictim d .=> age c .< age d)

  -- Ensure certain pairs can't be twins
  constrain $ age husband ./= age brother
  constrain $ age husband ./= age alice

  query $ do cs <- checkSat
             case cs of
               Sat -> do a <- getPerson alice
                         h <- getPerson husband
                         b <- getPerson brother
                         d <- getPerson daughter
                         s <- getPerson son
                         pure [a, h, b, d, s]
               _   -> error $ "Solver said: " ++ show cs
