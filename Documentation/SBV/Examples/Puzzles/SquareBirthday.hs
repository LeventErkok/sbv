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
import Data.SBV.Control

import qualified Data.SBV.List  as SL
import qualified Data.SBV.Tuple as ST

-- | Months in a year.
data Month = Jan | Feb | Mar | Apr | May | Jun
           | Jul | Aug | Sep | Oct | Nov | Dec
           deriving Show

-- | A date. We use unbounded integers for day and year, which simplifies coding,
-- though one can also enumerate the possible values from the problem itself.
data Date = MkDate { day   :: Integer
                   , month :: Month
                   , year  :: Integer
                   }

-- | Make 'Month' and 'Date' usable in symbolic contexts.
mkSymbolic [''Month, ''Date]

-- | Show instance for date, for pretty-printing.
instance Show Date where
  show (MkDate d m y) = show m ++ " " ++ pad ++ show d ++ ", " ++ show y
   where pad | d < 10 = " "
             | True   = ""

-- | Get a symbolic date with the given name. Since we used
-- integers for the day and year fields, we constrain them
-- appropriately. Note that one can further constrain days
-- based on the year and month; but that level detail isn't
-- necessary for the current problem.
symDate :: String -> Symbolic SDate
symDate nm = do dt <- free nm

                constrain [sCase|Date dt of
                              MkDate d _ y -> sAnd [ 1 .<= d, d .<= 31
                                                   , 0 .<= y
                                                   ]
                          |]

                pure dt

-- | Encode today as a symbolic value. The puzzle says today is June 1st, 2025.
today :: SDate
today = literal $ MkDate { day   =    1
                         , month =  Jun
                         , year  = 2025
                         }

-- | A date is on or after another, if the month-day combo is
-- lexicographically later. Note that we ignore the year for this
-- comparison, as we're interested if the anniversary of a date is after or not.
onOrAfter :: SDate -> SDate -> SBool
d1 `onOrAfter` d2 = (smonth d1, sday d1) .>= (smonth d2, sday d2)

-- | Similar to 'onOrAfter', except we require strictly later.
after :: SDate -> SDate -> SBool
d1 `after` d2 = (smonth d1, sday d1) .>  (smonth d2, sday d2)

-- | The age based on a given date is the difference between years less than one.
-- We have to adjust by 1 if today happens to be after the given date.
age :: SDate -> SInteger
age d = syear today - syear d - 1 + oneIf (today `after` d)

-- | We can let years to range over arbitrary integers. But that complicates the
-- job of the solver. So, based on what we know from the problem, we restrict
-- our attention to years betweek 1900 and 2100. Note that there are only
-- two years that satisfy this in that range: 1936 and 2025. (Any other square
-- year makes no sense for the setting of the problem.) To simplify the square-root
-- computation, we also store the square root in this list as the second component:
--
-- >>> squareYears
-- [(1936,44),(2025,45)]
squareYears :: [(Integer, Integer)]
squareYears = takeWhile (\(y, _) -> y < 2100)
            $ dropWhile (\(y, _) -> y < 1900)
            $ [(i * i, i) | i <- [1::Integer ..]]

-- | A date is square if all its components are.
squareDate :: SDate -> SBool
squareDate dt = [sCase|Date dt of
                   MkDate d m y -> squareDay d .&& squareMonth m .&& squareYear y
                |]
  where squareDay   d = d `sElem` [1, 4, 9, 16, 25]
        squareMonth m = m `sElem` [sJan, sApr, sSep]
        squareYear  y = y `sElem` map (literal . fst) squareYears


-- | Summing the square-roots of the components of a date.
sqrSum :: SDate -> SInteger
sqrSum dt = [sCase|Date dt of
               MkDate d m y -> r d + mr m + r y
            |]
 where r v  = v `SL.lookup` literal ([(i * i, i) | i <- [1, 2, 3, 4, 5]] ++ squareYears)

       mr :: SMonth -> SInteger
       mr m = [sCase|Month m of
                  Jan -> 1
                  Apr -> 2
                  Sep -> 3
                  _   -> some "Non-Square Month" (const sTrue)
              |]

-- | Formalizing the puzzle. We literally write down the description in
-- SBV notation. As with any formalization, this step is subjective; there
-- could be many different ways to express the same problem. The description
-- below is quite faithful to the problem description given. We have:
--
-- >>> puzzle
-- Me : Sep 25, 1971
-- Mom: Aug  1, 1936
puzzle :: IO ()
puzzle = runSMT $ do

    -----------------------------------
    -- Constraints about my birthday
    -----------------------------------
    myBirthday <- symDate "My Birthday"

    -- I was born in the last millenium
    constrain $ syear myBirthday .< 2000 .&& syear myBirthday .>= 1900

    -- My next birthday will be a square
    let next = [sCase|Date myBirthday of
                  MkDate d m _ -> sMkDate d m (syear today + oneIf (today `onOrAfter` myBirthday))
               |]

    constrain $ squareDate next

    -- And it'll be the last square day of my life, so we maximize the metric corresponding to the
    -- date. We turn it into a 3-tuple of year, month, date over integers, which preserves the
    -- order of the dates.
    maximize "Next Birthday Latest" $ ST.tuple (syear next, fromEnum (smonth next), sday next)

    -- If you square the components of my next birthday, it gives me my current age on Jun 1, 2025
    constrain $ sqrSum next .== age myBirthday

    -----------------------------------
    -- Constraints about mom's birthday
    -----------------------------------
    momBirthday <- symDate "Mom's Birthday"

    -- Mom has a square birth-date, except for the month:
    constrain [sCase|Date momBirthday of
                 MkDate d _ y -> squareDate (sMkDate d sJan y)
              |]

    -- Mom's day and month are perfect cubes
    constrain [sCase|Date momBirthday of
                 MkDate d m _ -> sAnd [ d `sElem` [1, 8, 27]
                                      , m `sElem` [sJan, sAug]
                                      ]
              |]

    -- Extract the results:
    query $ do cs <- checkSat
               case cs of
                 Sat -> do me  <- getValue myBirthday
                           mom <- getValue momBirthday

                           io $ do putStrLn $ "Me : " ++ show me
                                   putStrLn $ "Mom: " ++ show mom

                 _   -> error $ "Unexpected result: " ++ show cs
