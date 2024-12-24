{-# OPTIONS_GHC -Wall -Werror #-}

module Main where

import Data.Char
import Data.List
import qualified Control.Exception as C

verbose :: Bool
verbose = False

msg :: String -> IO ()
msg s | verbose = putStrLn $ "HADDOCK SIMPLIFY: " ++ s
      | True    = pure ()

main :: IO ()
main = go False Nothing

go :: Bool -> Maybe String -> IO ()
go failed mbInp = do
  mbLn <- case mbInp of
           Just s  -> pure $ Just s
           Nothing -> (Just <$> getLine) `C.catch` (\(_ :: C.SomeException) -> return Nothing)
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
                                     go failed Nothing
                             else do msg ln
                                     msg l1
                                     msg l2
                                     msg l3
                                     msg l4
                                     msg l5
                                     go failed Nothing
                  else if "Warning: " `isPrefixOf` ln && ": could not find link destinations for:" `isInfixOf` ln
                          then do let skip = do l <- getLine
                                                if ("-" `isPrefixOf` dropWhile isSpace l)
                                                   then skip
                                                   else pure l
                                  l <- skip
                                  go failed (Just l)
                          else do putStrLn ln
                                  go (failed || bad ln) Nothing

bad :: String -> Bool
bad ln
  | '%' `notElem` ln
  = False
  | True
  = case words ln of
     "100%" : _ -> False
     _          -> True
