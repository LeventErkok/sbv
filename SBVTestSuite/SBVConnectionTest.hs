{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Main (main) where

import Data.SBV
import Data.List
import Control.Monad
import System.Exit
import System.Environment

-- Known solvers with bugs! Should really be empty!
badSolvers :: [SMTConfig]
badSolvers = []

solverName :: SMTConfig -> String
solverName = show . name . solver

main :: IO ()
main = do let allSolvers = map (\s -> (solverName s, s)) [abc, boolector, bitwuzla, cvc4, cvc5, mathSAT, yices, z3, dReal]

          args <- getArgs

          let chosenSolvers = case args of
                               [] -> allSolvers
                               _  -> let walk []     = []
                                         walk (c:cs) = case c `lookup` allSolvers of
                                                         Nothing -> error $ "Unknown chosen solver: " ++ show c
                                                         Just s  -> (c, s) : walk cs
                                     in walk args

              (requiredBad, requiredPresent) = partition (\(n, _) -> n `elem` map solverName badSolvers) chosenSolvers

              pickTest s = case name (solver s) of
                             DReal -> testI s
                             _     -> test  s

          mapM_ (pickTest . snd) requiredPresent

          let tested   = sort $ map fst requiredPresent
              allKnown = sort $ map fst allSolvers

              skipped  = filter (`notElem` tested) allKnown


          putStrLn $ "Tested OK basic connection to: " ++ intercalate ", " (map fst requiredPresent)
          unless (null requiredBad) $ putStrLn $ "*** NB: The following solvers are declared bad: " ++ intercalate ", " (map (\(n, s)-> show (n, solverName s)) requiredBad)
          unless (null skipped)     $ putStrLn $ "*** NB: The following solvers are skipped: "      ++ intercalate ", " skipped

test :: SMTConfig -> IO ()
test s = do check  s "t0" t0 (== False)
            check  s "t1" t1 (== True)
            models "t2" t2 (== ([2,62,66,126,130,190,194,254]::[Word8]))
            models "t3" t3 (== ([]::[Word8]))
            models "t4" t4 (== [4::Word8])
  where models m p f = allSat p >>= (decide s m f . sort) . extractModels
        t0 x = x   .== x+(1::SWord8)
        t1 x = x*2 .== x+(x::SWord8)
        t2 x = x*x .== (4::SWord8)
        t3 x = x*x .== (3::SWord8)
        t4 x = x*3 .== (12::SWord8)

-- integer only test, for dReal mostly
testI :: SMTConfig -> IO ()
testI s = do check s "t0" t0 (== True)
             check s "t1" t1 (== False)
  where t0 x = x .== (x :: SReal)
        t1 x = x .== (2 :: SReal) .&& (x .== 3)

check :: Provable a => SMTConfig -> String -> a -> (Bool -> Bool) -> IO ()
check s m p f = isTheoremWith s p >>= decide s m f

decide :: Show a => SMTConfig -> String -> (a -> Bool) -> a -> IO ()
decide s m f r
  | f r  = return ()
  | True = do putStrLn $ m ++ "[" ++ solverName s ++ "] FAIL. Got: " ++ show r
              exitFailure
