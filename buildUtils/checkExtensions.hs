{-# OPTIONS_GHC -Wall -Werror #-}

module Main where

import Data.Char
import Data.List
import Control.Monad
import System.Exit

main :: IO ()
main = do
  required <- words <$> readFile "required_extensions"

  let hd (x:_) = x
      hd []    = error "impossible, hd received empty list on words"

      process = sort . filter (isUpper . hd) . takeWhile (/= "Library") . drop 1 . dropWhile (/= "other-extensions:")

  found <- process . words <$> readFile "sbv.cabal"

  let extras = found    \\ required
      need   = required \\ found

  unless (null extras) $ do
    putStrLn "EXTRAS (should be removed)"
    mapM_ (putStrLn . ("  " ++)) extras

  unless (null need) $ do
    putStrLn "NEEDED (should be added)"
    mapM_ (putStrLn . ("  " ++)) need

  if null (extras ++ need)
     then do putStrLn "*** CHECK EXTENSIONS passed."
             exitSuccess
     else exitFailure
