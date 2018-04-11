-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Puzzles.RegexCrossword
-- Copyright   :  (c) Joel Burget
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- This example solves regex crosswords from https://regexcrossword.com/.
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}

module Data.SBV.Examples.Strings.RegexCrossword (solveCrosswords) where

import Control.Monad (forM, forM_)
import qualified Data.Map as Map
import Data.SBV

-- | We specify a crossword as the list of regexes constraining its rows and
-- columns.
data RegexCrossword = RegexCrossword [SRegExp] [SRegExp]

solveCrossword :: RegexCrossword -> IO ()
solveCrossword (RegexCrossword rowRegexps colRegexps) = do
  solvedRows <- getModelDictionaries <$> allSat puzzle
  let numRows = length rowRegexps
  case solvedRows of
    [solvedRows'] ->
      forM_ [1..numRows] $ \n ->
        case Map.lookup ("row-" ++ show n) solvedRows' of
          Nothing -> putStrLn "(unexpected) row not found"
          Just solvedRow -> print solvedRow
    []                 -> error "no solution"
    _                  -> error "no unique solution"

  where lit = literal . fromIntegral
        puzzle = do
          let numRows = length rowRegexps
              numCols = length colRegexps

          -- constrain rows
          rowVars <- forM [1..numRows] $ \rowN ->
            free ("row-" ++ show rowN)
          forM_ (zip rowVars rowRegexps) $ \(rowVar, rowRegexp) -> do
            constrain $ strMatch rowVar rowRegexp
            constrain $ strLen rowVar .== lit numCols

          -- constrain columns
          colVars <- mkFreeVars numCols
          forM_ (zip colVars colRegexps) $ \(colVar, colRegexp) -> do
            constrain $ strMatch colVar colRegexp
            constrain $ strLen colVar .== lit numRows

          -- constrain intersections
          forM_ [0..numRows - 1] $ \rowN ->
            forM_ [0..numCols - 1] $ \colN ->
              let row = rowVars !! rowN
                  col = colVars !! colN
              in constrain $ strAt row (lit colN)
                         .== strAt col (lit rowN)

-- Helper to define a character class.
reClass :: String -> SRegExp
reClass = foldr (\char re -> RE_Literal [char] + re) RE_None

-- | Solve three example crosswords:
--
-- >>> solveCrossword
-- puzzle 1:
-- "ATO" :: String
-- "WEL" :: String
-- puzzle 2:
-- "WA" :: String
-- "LK" :: String
-- "ER" :: String
-- puzzle 3:
-- "RATS" :: String
-- "ABUT" :: String
-- "TUBA" :: String
-- "STAR" :: String
solveCrosswords :: IO ()
solveCrosswords = do
  -- https://regexcrossword.com/challenges/intermediate/puzzles/1
  putStrLn "puzzle 1:"
  solveCrossword $ RegexCrossword
    [ RE_Star (reClass "NOTAD")  -- [NOTAD]*
    , "WEL" + "BAL" + "EAR" -- WEL|BAL|EAR
    ]

    [ "UB" + "IE" + "AW" -- UB|IE|AW
    , RE_Star (reClass "TUBE") -- [TUBE]*
    , reClass "BORF" * RE_All -- [BORF].
    ]

  -- https://regexcrossword.com/challenges/intermediate/puzzles/2
  putStrLn "\npuzzle 2:"
  solveCrossword $ RegexCrossword
    [ RE_Plus (reClass "AWE") -- [AWE]+
    , RE_Plus (reClass "ALP") * "K" -- [ALP]+K
    , "PR" + "ER" + "EP" -- (PR|ER|EP)
    ]

    [ reClass "BQW" * ("PR" + "LE") -- [BQW](PR|LE)
    , RE_Plus (reClass "RANK") -- [RANK]+
    ]

  -- https://regexcrossword.com/challenges/palindromeda/puzzles/3
  putStrLn "\npuzzle 3:"
  solveCrossword $ RegexCrossword
    [ RE_Star (reClass "TRASH") -- [TRASH]*
    , ("AF" + "AB") * RE_Star (reClass "TUP") -- (FA|AB)[TUP]*
    , RE_Star ("BA" + "TH" + "TU") -- (BA|TH|TU)*
    , RE_Star RE_All * "A" * RE_Star RE_All -- .*A.*
    ]

    [ RE_Star ("TS" + "RA" + "QA") -- (TS|RA|QA)*
    , RE_Star ("AB" + "UT" + "AR") -- (AB|UT|AR)*
    , ("K" + "T") * "U" * RE_Star RE_All * ("A" + "R") -- (K|T)U.*(A|R)
    , RE_Plus ("AR" + "FS" + "ST")-- (AR|FS|ST)+
    ]
