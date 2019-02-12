-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Queries.Sums
-- Copyright   :  (c) Joel Burget
--                    Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Testing sum queries
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module TestSuite.Queries.Sums (tests)  where

import Data.SBV
import Data.SBV.Control
import Data.SBV.Either as E
import Data.SBV.Maybe  as M

import qualified Data.SBV.List as L

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.QuerySums"
    [ goldenCapturedIO "query_Sums"         $ testQuery querySums
    , goldenCapturedIO "query_ListOfSum"    $ testQuery queryListOfSum
    , goldenCapturedIO "query_Maybe"        $ testQuery queryMaybe
    , goldenCapturedIO "query_ListOfMaybe"  $ testQuery queryListOfMaybe
    , goldenCapturedIO "query_SumMaybeBoth" $ testQuery querySumMaybeBoth
    ]

testQuery :: Show a => Symbolic a -> FilePath -> IO ()
testQuery t rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} t
                    appendFile rf ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")

querySums :: Symbolic (Either Integer Char)
querySums = do
  a <- sEither @Integer @Char "a"

  constrain $ E.either (.== 1) (const sFalse) a

  query $ do
    _ <- checkSat

    av <- getValue a

    if av == Left 1
       then return av
       else error $ "Didn't expect this: " ++ show av

queryListOfSum :: Symbolic [Either Integer Char]
queryListOfSum = do
  lst <- sList @(Either Integer Char) "lst"
  constrain $ L.length lst .== 2
  constrain $ isLeft $ L.head lst
  constrain $ isRight $ L.head $ L.tail lst

  query $ do
    _  <- checkSat
    av <- getValue lst

    case av of
      [Left _, Right _] -> return av
      _                 -> error $ "Didn't expect this: " ++ show av

queryMaybe :: Symbolic (Maybe Integer)
queryMaybe = do
  a <- sMaybe @Integer "a"

  constrain $ M.maybe sFalse (.== 1) a

  query $ do
    _ <- checkSat

    av <- getValue a

    if av == Just 1
       then return av
       else error $ "Didn't expect this: " ++ show av

queryListOfMaybe :: Symbolic [Maybe Char]
queryListOfMaybe = do
  lst <- sList @(Maybe Char) "lst"
  constrain $ L.length lst .== 2
  constrain $ isJust $ L.head lst
  constrain $ isNothing $ L.head $ L.tail lst

  query $ do
    _  <- checkSat
    av <- getValue lst

    case av of
      [Just _, Nothing] -> return av
      _                 -> error $ "Didn't expect this: " ++ show av

querySumMaybeBoth :: Symbolic (Either Integer Integer, Maybe Integer)
querySumMaybeBoth = query $ do
        (x :: SEither Integer Integer) <- freshVar_
        (y :: SMaybe Integer)          <- freshVar_

        constrain $ isLeft x
        constrain $ isJust y

        _ <- checkSat
        xv <- getValue x
        yv <- getValue y
        return (xv, yv)
