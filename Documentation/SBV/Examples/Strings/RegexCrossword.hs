-----------------------------------------------------------------------------
-- |
-- Module      :  Documentation.SBV.Examples.Puzzles.RegexCrossword
-- Copyright   :  (c) Joel Burget
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- This example solves regex crosswords from <http://regexcrossword.com>
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}

module Documentation.SBV.Examples.Strings.RegexCrossword where

import Data.List (genericLength, transpose)

import Data.SBV
import Data.SBV.Control

import qualified Data.SBV.String as S
import qualified Data.SBV.RegExp as R

-- | Solve a given crossword, returning the corresponding rows
solveCrossword :: [SRegExp] -> [SRegExp] -> IO [String]
solveCrossword rowRegExps colRegExps = runSMT $ do
        let numRows = genericLength rowRegExps
            numCols = genericLength colRegExps

        -- constrain rows
        let mkRow rowRegExp = do row <- free_
                                 constrain $ row `R.match` rowRegExp
                                 constrain $ S.length row .== literal numCols
                                 return row

        rows <- mapM mkRow rowRegExps

        -- constrain colums
        let mkCol colRegExp = do col <- free_
                                 constrain $ col `R.match` colRegExp
                                 constrain $ S.length col .== literal numRows
                                 return col

        cols <- mapM mkCol colRegExps

        -- constrain each "cell" as they rows/columns intersect:
        let rowss =           [[r .!! literal i | i <- [0..numCols-1]] | r <- rows]
        let colss = transpose [[c .!! literal i | i <- [0..numRows-1]] | c <- cols]

        constrain $ bAnd $ zipWith (.==) (concat rowss) (concat colss)

        -- Now query to extract the solution
        query $ do cs <- checkSat
                   case cs of
                     Unk   -> error "Solver returned unknown!"
                     Unsat -> error "There are no solutions to this puzzle!"
                     Sat   -> mapM getValue rows

-- | Helper to define a character class.
reClass :: String -> SRegExp
reClass = foldr (\char re -> RE_Literal [char] + re) RE_None

-- | Solve <http://regexcrossword.com/challenges/intermediate/puzzles/1>
--
-- >>> puzzle1
-- ["ATO","WEL"]
puzzle1 :: IO [String]
puzzle1 = solveCrossword rs cs
  where rs = [ RE_Star (reClass "NOTAD")  -- [NOTAD]*
             , "WEL" + "BAL" + "EAR"      -- WEL|BAL|EAR
             ]

        cs = [ "UB" + "IE" + "AW"         -- UB|IE|AW
             , RE_Star (reClass "TUBE")   -- [TUBE]*
             , reClass "BORF" * RE_All    -- [BORF].
             ]

-- | Solve <http://regexcrossword.com/challenges/intermediate/puzzles/2>
--
-- >>> puzzle2
-- ["WA","LK","ER"]
puzzle2 :: IO [String]
puzzle2 = solveCrossword rs cs
  where rs = [ RE_Plus (reClass "AWE")       -- [AWE]+
             , RE_Plus (reClass "ALP") * "K" -- [ALP]+K
             , "PR" + "ER" + "EP"            -- (PR|ER|EP)
             ]

        cs = [ reClass "BQW" * ("PR" + "LE") -- [BQW](PR|LE)
             , RE_Plus (reClass "RANK")      -- [RANK]+
             ]

-- | Solve <http://regexcrossword.com/challenges/palindromeda/puzzles/3>
--
-- >>> puzzle3
-- ["RATS","ABUT","TUBA","STAR"]
puzzle3 :: IO [String]
puzzle3 = solveCrossword rs cs
 where rs = [ RE_Star (reClass "TRASH")                       -- [TRASH]*
            , ("FA" + "AB") * RE_Star (reClass "TUP")         -- (FA|AB)[TUP]*
            , RE_Star ("BA" + "TH" + "TU")                    -- (BA|TH|TU)*
            , RE_Star RE_All * "A" * RE_Star RE_All           -- .*A.*
            ]

       cs = [ RE_Star ("TS" + "RA" + "QA")                     -- (TS|RA|QA)*
            , RE_Star ("AB" + "UT" + "AR")                     -- (AB|UT|AR)*
            , ("K" + "T") * "U" * RE_Star RE_All * ("A" + "R") -- (K|T)U.*(A|R)
            , RE_Plus ("AR" + "FS" + "ST")                     -- (AR|FS|ST)+
            ]
