{-# OPTIONS_GHC -Wall -Werror #-}

module Main where

import System.Environment (getArgs)
import System.Exit
import System.Process

main :: IO ()
main = getArgs >>= go

start :: String -> IO ()
start = go . words

go :: [String] -> IO ()
go [goldFile, "1"] = check True  goldFile
go [goldFile]      = check False goldFile
go as              = do putStrLn $ "** Incorrect arguments: " ++ show as
                        exitFailure

check :: Bool -> FilePath -> IO ()
check accept gold = do
   let current  = gold    ++ "_temp"
       relevant = current ++ "_relevant"

   ls <- lines <$> readFile current

   let curOutput = unlines (take 3 (reverse (take 6 (reverse ls))))
   writeFile relevant curOutput

   -- Do a diff
   ec <- rawSystem "/usr/bin/git" (words ("diff -U0 --word-diff --no-index -- " ++ gold ++ " " ++ relevant))
   _  <- rawSystem "/bin/rm" (words ("-f " ++ relevant))

   case ec of
     ExitSuccess   -> do putStrLn "*** Doctest output matches."
     ExitFailure{} -> do putStrLn "*** Doctest have different results."
                         if accept
                            then do putStrLn "*** ACCEPTING the new file."
                                    writeFile gold curOutput
                            else exitWith ec
