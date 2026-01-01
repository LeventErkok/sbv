-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.SquareBirthday
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- As of January 2026, to access the careers link at <http://math.inc>, you need to solve the following
-- puzzle:
--
-- @
-- Suppose that today is June 1, 2025. We call a date "square" if all of its components (day, month, and year) are
-- perfect squares. I was born in the last millennium, and my next birthday (relative to that date) will be the last
-- square date in my life. If you sum the square roots of the components of that upcoming square birthday
-- (day, month, year), you obtain my age on June 1, 2025. My mother would have been born on a square date if the month
-- were a square number; in reality it is not a square date, but both the month and day are perfect cubes. When was
-- I born, and when was my mother born?
-- @
--
-- So, let's solve it using SBV.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE OverloadedRecordDot #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.SquareBirthday where

import Prelude hiding (fromEnum, toEnum)

import Data.SBV
import qualified Data.SBV.List as SL

data Month = Jan | Feb | Mar | Apr | May | Jun
           | Jul | Aug | Sep | Oct | Nov | Dec
           deriving Show

data Date  = Date { day   :: Integer
                  , month :: Month
                  , year  :: Integer
                  }

mkSymbolic [''Month, ''Date]

instance Show Date where
  show (Date d m y) = show m ++ " " ++ show d ++ ", " ++ show y

symDate :: String -> Symbolic SDate
symDate nm = do dt <- free nm

                constrain [sCase|Date dt of
                              Date d _ y -> sAnd [ 1 .<= d, d .<= 31
                                                 , 0 .<= y
                                                 ]
                          |]

                pure dt

today :: SDate
today = literal $ Date { day   =    1
                       , month =  Jun
                       , year  = 2025
                       }

after, onOrAfter :: SDate -> SDate -> SBool
d1 `onOrAfter` d2 = (smonth d1, sday d1) .>= (smonth d2, sday d2)
d1 `after`     d2 = (smonth d1, sday d1) .>  (smonth d2, sday d2)

age :: SDate -> SInteger
age d = syear today - syear d - 1 + oneIf (today `after` d)

squareDay :: SInteger -> SBool
squareDay d = d `sElem` [1, 4, 9, 16, 25]

squareMonth :: SMonth -> SBool
squareMonth m = m `sElem` [sJan, sApr, sSep]

squareYears :: [(Integer, Integer)]
squareYears = takeWhile (\(y, _) -> y < 2100)
            $ dropWhile (\(y, _) -> y < 1900)
            $ [(i * i, i) | i <- [1::Integer ..]]

squareYear :: SInteger -> SBool
squareYear y = y `sElem` map (literal . fst) squareYears

squareDate :: SDate -> SBool
squareDate dt = [sCase|Date dt of
                   Date d m y -> squareDay d .&& squareMonth m .&& squareYear y
                |]

sqrSum :: SDate -> SInteger
sqrSum dt = [sCase|Date dt of
               Date d m y -> r d + mr m + r y
            |]
 where r v  = v `SL.lookup` literal ([(i * i, i) | i <- [1, 2, 3, 4, 5]] ++ squareYears)

       mr :: SMonth -> SInteger
       mr m = [sCase|Month m of
                  Jan -> 1
                  Apr -> 2
                  Sep -> 3
                  _   -> some "Non-Square Month" (const sTrue)
              |]

instance Metric Date where
  type MetricSpace Date = Integer
  toMetricSpace dt  = [sCase|Date dt of
                         Date d m y -> y*10000 +  fromEnum m*100 + d
                      |]
  fromMetricSpace t = let (y, r) = t `sDivMod` 10000
                          (m, d) = r `sDivMod`   100
                      in sDate d (toEnum m) y
  annotateForMS _ s = "toMetricSpace(" ++ s ++ ")"

-- | Solve the puzzle:
--
-- >>> optimizeWith z3{isNonModelVar = (\v -> any (`elem` v) "@(") } Lexicographic puzzle
puzzle :: ConstraintSet
puzzle = do

       myBirthday <- symDate "My Birthday"

       -- I was born in the last millenium
       constrain $ syear myBirthday .< 2000 .&& syear myBirthday .>= 1900

       -- My next birthday will be a square
       let next = [sCase|Date myBirthday of
                     Date d m _ -> sDate d m (syear today + oneIf (today `onOrAfter` myBirthday))
                  |]

       constrain $ squareDate next

       -- And it'll be the last square day of my life:
       maximize "@Next Birthday" next

       -- If you square the components of my next birthday, it gives me my current age on Jun 1, 2025
       let ageOnJun1 = age myBirthday
       constrain $ sqrSum next .== ageOnJun1

       momBirthday <- symDate "Mom's Birthday"

       -- Mom has a square birth-date, except for the month:
       constrain [sCase|Date momBirthday of
                    Date d _ y -> squareDate (sDate d sJan y)
                 |]

       -- Mom's day and month are perfect cubes
       constrain [sCase|Date momBirthday of
                    Date d m _ -> sAnd [ d `sElem` [1, 8, 27]
                                       , m `sElem` [sJan, sAug]
                                       ]
                 |]
