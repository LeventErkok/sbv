{-# OPTIONS_GHC -Wall -Werror #-}

module Main where

import Data.List
import qualified Control.Exception as C

verbose :: Bool
verbose = False

msg :: String -> IO ()
msg s | verbose = putStrLn $ "HADDOCK SIMPLIFY: " ++ s
      | True    = pure ()

main :: IO ()
main = do
  mbLn <- (Just <$> getLine) `C.catch` (\(_ :: C.SomeException) -> return Nothing)
  case mbLn of
    Nothing -> pure ()
    Just ln -> if "Warning: '" `isPrefixOf` ln && "' is ambiguous. It is defined" `isSuffixOf` ln
                  then do l1 <- getLine
                          l2 <- getLine
                          l3 <- getLine
                          l4 <- getLine
                          l5 <- getLine
                          if    l1 == "    You may be able to disambiguate the identifier by qualifying it or"
                             && l2 == "    by specifying the type/value namespace explicitly."
                             then do msg "Skipped lines"
                                     main
                             else do msg ln
                                     msg l1
                                     msg l2
                                     msg l3
                                     msg l4
                                     msg l5
                                     main
                  else do putStrLn ln
                          main
