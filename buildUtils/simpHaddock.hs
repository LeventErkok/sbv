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
main = go False

go :: Bool -> IO ()
go failed = do
  mbLn <- (Just <$> getLine) `C.catch` (\(_ :: C.SomeException) -> return Nothing)
  case mbLn of
    Nothing -> if failed
                  then error "*** There were files that had missing haddock-documentation. Stopping."
                  else pure ()
    Just ln -> if "Warning: '" `isPrefixOf` ln && "' is ambiguous. It is defined" `isSuffixOf` ln
                  then do l1 <- getLine
                          l2 <- getLine
                          l3 <- getLine
                          l4 <- getLine
                          l5 <- getLine
                          if    l1 == "    You may be able to disambiguate the identifier by qualifying it or"
                             && l2 == "    by specifying the type/value namespace explicitly."
                             then do msg "Skipped lines"
                                     go failed
                             else do msg ln
                                     msg l1
                                     msg l2
                                     msg l3
                                     msg l4
                                     msg l5
                                     go failed
                  else do putStrLn ln
                          go (failed || bad ln)

bad :: String -> Bool
bad ln
  | '%' `notElem` ln
  = False
  | True
  = case words ln of
     "100%" : _ -> False
     _          -> True
