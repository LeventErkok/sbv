{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

-- Executable examples accompanying the SBV experience-report draft.
module Main (main) where

import Control.Monad (unless, void)
import Data.List (sort)
import System.Environment (getArgs)
import qualified System.Timeout as Timeout

import Data.SBV
import Data.SBV.Control
import qualified Data.SBV.List as SL
import Data.SBV.TP
import Data.SBV.Tools.CodeGen
import qualified Documentation.SBV.Examples.TP.ConstFold as CF

-- BEGIN saturating
satAdd :: SWord8 -> SWord8 -> SWord8
satAdd x y = ite (x .> 255 - y) 255 (x + y)

satAddSpec :: SWord8 -> SWord8 -> SBool
satAddSpec x y = sFromIntegral (satAdd x y) .==
                ite (total .> 255) 255 total
  where total = sFromIntegral x + sFromIntegral y :: SInteger
-- END saturating

-- BEGIN roots
roots :: IO [Integer]
roots = runSMT $ do
  x <- sInteger "x"
  constrain $ x * x .== 9
  query $ let loop = do
                result <- checkSat
                case result of
                  Sat -> do v <- getValue x
                            constrain $ x ./= literal v
                            (v :) <$> loop
                  Unsat -> pure []
                  _ -> io $ fail "Root enumeration was inconclusive"
          in loop
-- END roots

-- BEGIN datatype
data Box a = Box a deriving (Eq, Ord, Show)
mkSymbolic [''Box]

lateDatatype :: IO CheckSatResult
lateDatatype = runSMT $ query $ do
  x <- freshVar @(Box Word8) "x"
  y <- freshVar @(Box Word8) "y"
  constrain $ x ./= y
  checkSat
-- END datatype

-- BEGIN reverse
revAcc :: SList Integer -> SList Integer -> SList Integer
revAcc = smtFunction "paper.revAcc" $ \acc xs ->
  [sCase| xs of
    []     -> acc
    x : xt -> revAcc (x .: acc) xt
  |]

revAccCorrect :: TP (Proof (Forall "xs" [Integer]
                        -> Forall "acc" [Integer] -> SBool))
revAccCorrect = induct "revAccCorrect"
  (\(Forall xs) (Forall acc) ->
      revAcc acc xs .== SL.reverse xs SL.++ acc) $
  \ih (x, xs) acc -> [] |- revAcc acc (x .: xs)
                       =: revAcc (x .: acc) xs
                       ?? ih
                       =: SL.reverse xs SL.++ (x .: acc)
                       =: (SL.reverse xs SL.++ [x]) SL.++ acc
                       =: SL.reverse (x .: xs) SL.++ acc
                       =: qed
-- END reverse

-- BEGIN codegen
generateAdder :: FilePath -> IO ()
generateAdder dir = compileToC (Just dir) "sat_add" $ do
  cgOverwriteFiles True
  cgGenerateDriver False
  x <- cgInput "x"
  y <- cgInput "y"
  cgReturn $ satAdd x y
-- END codegen

check :: String -> IO Bool -> IO ()
check name action = do
  result <- Timeout.timeout (120 * 1000000) action
  unless (result == Just True) $ fail (name ++ ": failed or timed out")
  putStrLn $ "PASS " ++ name

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--const-fold"] -> check "constant folding (CVC5)" $
      runTPWith cvc5 CF.cfoldCorrect >> pure True
    ["--generate", dir] -> generateAdder dir
    [] -> do
      check "integer successor" $
        isTheorem $ \x -> x + 1 .> (x :: SInteger)
      check "Int8 counterexample is 127" $ do
        r <- prove $ do x <- sInt8 "x"
                        pure $ x + 1 .> x
        print r
        pure $ getModelValue "x" r == Just (127 :: Int8)
      check "float reflexivity counterexample is NaN" $ do
        r <- prove $ do x <- sFloat "x"
                        pure $ x .== x
        print r
        pure $ maybe False isNaN (getModelValue "x" r :: Maybe Float)
      check "saturating addition theorem" $ isTheorem satAddSpec
      check "incremental enumeration" $ (== [-3, 3]) . sort <$> roots
      check "datatype first introduced during query" $ (== Sat) <$> lateDatatype
      check "accumulator reversal induction" $ void (runTP revAccCorrect) >> pure True
    _ -> fail "Usage: paper-examples [--const-fold | --generate DIR]"
