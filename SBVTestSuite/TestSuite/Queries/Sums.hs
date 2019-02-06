-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Queries.Sums
-- Copyright   :  (c) Levent Erkok
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
import Data.SBV.Sum
import qualified Data.SBV.List as L

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.QuerySums"
    [ goldenCapturedIO "query_Sums"      $ testQuery querySums
    , goldenCapturedIO "query_ListOfSum" $ testQuery queryListOfSum
    ]

testQuery :: Show a => Symbolic a -> FilePath -> IO ()
testQuery t rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} t
                    appendFile rf ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")

querySums :: Symbolic (Either Integer Char)
querySums = do
  a <- sSum @Integer @Char "a"

  constrain $ case_ a (.== 1) (const sFalse)

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
