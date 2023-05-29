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

{-# OPTIONS_GHC -Wall -Werror #-}

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
    [ goldenCapturedIO "query_Sums"            $ testQuery querySums
    , goldenCapturedIO "query_ListOfSum"       $ testQuery queryListOfSum
    , goldenCapturedIO "query_Maybe"           $ testQuery queryMaybe
    , goldenCapturedIO "query_ListOfMaybe"     $ testQuery queryListOfMaybe
    , goldenCapturedIO "query_SumMaybeBoth"    $ testQuery querySumMaybeBoth
    , goldenCapturedIO "query_sumMergeMaybe1"  $ testQuery querySumMergeMaybe1
    , goldenCapturedIO "query_sumMergeMaybe2"  $ testQuery querySumMergeMaybe2
    , goldenCapturedIO "query_sumMergeEither1" $ testQuery querySumMergeEither1
    , goldenCapturedIO "query_sumMergeEither2" $ testQuery querySumMergeEither2
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

querySumMergeMaybe1 :: Symbolic (Maybe Integer, Maybe Integer, Bool)
querySumMergeMaybe1 = query $ do
   (x :: SMaybe Integer) <- freshVar_
   (y :: SMaybe Integer) <- freshVar_
   b  <- freshVar_

   constrain $ isNothing $ ite b x y

   _ <- checkSat
   xv <- getValue x
   yv <- getValue y
   bv <- getValue b
   return (xv, yv, bv)

querySumMergeMaybe2 :: Symbolic (Maybe Integer, Maybe Integer, Bool)
querySumMergeMaybe2 = query $ do
   (x :: SMaybe Integer) <- freshVar_
   (y :: SMaybe Integer) <- freshVar_
   b  <- freshVar_

   constrain $ isJust $ ite b x y

   _ <- checkSat
   xv <- getValue x
   yv <- getValue y
   bv <- getValue b
   return (xv, yv, bv)

querySumMergeEither1 :: Symbolic (Either Integer Bool, Either Integer Bool, Bool)
querySumMergeEither1 = query $ do
   (x :: SEither Integer Bool) <- freshVar_
   (y :: SEither Integer Bool) <- freshVar_
   b  <- freshVar_

   constrain $ isLeft $ ite b x y

   _ <- checkSat
   xv <- getValue x
   yv <- getValue y
   bv <- getValue b
   return (xv, yv, bv)

querySumMergeEither2 :: Symbolic (Either Integer Bool, Either Integer Bool, Bool)
querySumMergeEither2 = query $ do
   (x :: SEither Integer Bool) <- freshVar_
   (y :: SEither Integer Bool) <- freshVar_
   b  <- freshVar_

   constrain $ isRight $ ite b x y

   _ <- checkSat
   xv <- getValue x
   yv <- getValue y
   bv <- getValue b
   return (xv, yv, bv)

{- HLint ignore module "Reduce duplication" -}
