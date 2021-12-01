-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Strings.RegexCrossword
-- Copyright : (c) Joel Burget
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- This example solves regex crosswords from <http://regexcrossword.com>
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Strings.RegexCrossword where

import Data.List (genericLength, transpose)

import Data.SBV
import Data.SBV.Control

import Prelude hiding ((!!))
import Data.SBV.String ((!!))

import qualified Data.SBV.String as S
import qualified Data.SBV.RegExp as R

-- | Solve a given crossword, returning the corresponding rows
solveCrossword :: [R.RegExp] -> [R.RegExp] -> IO [String]
solveCrossword rowRegExps colRegExps = runSMT $ do
        let numRows = genericLength rowRegExps
            numCols = genericLength colRegExps

        -- constrain rows
        let mkRow rowRegExp = do row <- free_
                                 constrain $ row `R.match` rowRegExp
                                 constrain $ S.length row .== literal numCols
                                 return row

        rows <- mapM mkRow rowRegExps

        -- constrain columns
        let mkCol colRegExp = do col <- free_
                                 constrain $ col `R.match` colRegExp
                                 constrain $ S.length col .== literal numRows
                                 return col

        cols <- mapM mkCol colRegExps

        -- constrain each "cell" as they rows/columns intersect:
        let rowss =           [[r !! literal i | i <- [0..numCols-1]] | r <- rows]
        let colss = transpose [[c !! literal i | i <- [0..numRows-1]] | c <- cols]

        constrain $ sAnd $ zipWith (.==) (concat rowss) (concat colss)

        -- Now query to extract the solution
        query $ do cs <- checkSat
                   case cs of
                     Unk    -> error "Solver returned unknown!"
                     DSat{} -> error "Solver returned delta-sat!"
                     Unsat  -> error "There are no solutions to this puzzle!"
                     Sat    -> mapM getValue rows

-- | Solve <http://regexcrossword.com/challenges/intermediate/puzzles/1>
--
-- >>> puzzle1
-- ["ATO","WEL"]
puzzle1 :: IO [String]
puzzle1 = solveCrossword rs cs
  where rs = [ R.KStar (R.oneOf "NOTAD")  -- [NOTAD]*
             , "WEL" + "BAL" + "EAR"      -- WEL|BAL|EAR
             ]

        cs = [ "UB" + "IE" + "AW"         -- UB|IE|AW
             , R.KStar (R.oneOf "TUBE")   -- [TUBE]*
             , R.oneOf "BORF" * R.All     -- [BORF].
             ]

-- | Solve <http://regexcrossword.com/challenges/intermediate/puzzles/2>
--
-- >>> puzzle2
-- ["WA","LK","ER"]
puzzle2 :: IO [String]
puzzle2 = solveCrossword rs cs
  where rs = [ R.KPlus (R.oneOf "AWE")       -- [AWE]+
             , R.KPlus (R.oneOf "ALP") * "K" -- [ALP]+K
             , "PR" + "ER" + "EP"            -- (PR|ER|EP)
             ]

        cs = [ R.oneOf "BQW" * ("PR" + "LE") -- [BQW](PR|LE)
             , R.KPlus (R.oneOf "RANK")      -- [RANK]+
             ]

-- | Solve <http://regexcrossword.com/challenges/palindromeda/puzzles/3>
--
-- >>> puzzle3
-- ["RATS","ABUT","TUBA","STAR"]
puzzle3 :: IO [String]
puzzle3 = solveCrossword rs cs
 where rs = [ R.KStar (R.oneOf "TRASH")                -- [TRASH]*
            , ("FA" + "AB") * R.KStar (R.oneOf "TUP")  -- (FA|AB)[TUP]*
            , R.KStar ("BA" + "TH" + "TU")             -- (BA|TH|TU)*
            , R.KStar R.All * "A" * R.KStar R.All      -- .*A.*
            ]

       cs = [ R.KStar ("TS" + "RA" + "QA")                     -- (TS|RA|QA)*
            , R.KStar ("AB" + "UT" + "AR")                     -- (AB|UT|AR)*
            , ("K" + "T") * "U" * R.KStar R.All * ("A" + "R")  -- (K|T)U.*(A|R)
            , R.KPlus ("AR" + "FS" + "ST")                     -- (AR|FS|ST)+
            ]
