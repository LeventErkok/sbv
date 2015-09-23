module Main(main) where

import Control.Monad
import Data.Char
import Data.List
import System.IO

main :: IO ()
main = do hSetBuffering stdin  NoBuffering
          hSetBuffering stdout NoBuffering
          let loop = do end <- isEOF
                        unless end $ do i <- getLine
                                        case clean i of
                                          Nothing -> loop
                                          Just s  -> putStrLn s
                                        loop
          loop

clean :: String -> Maybe String
clean s
  | junk s    = Nothing
clean ('[':r) = Just $ extract False r
clean l       = Just l

extract :: Bool -> String -> String
extract th s = case words s of
                (n : "of" : m' : "Compiling" : "[TH]" : r)
                  -> extract True (unwords ([n, "of", m', "Compiling"] ++ r))
                (n : "of" : m' : "Compiling" : _)
                   | not (null m'), last m' == ']', all isDigit n, all isDigit (init m')
                  -> let (f, ']':r) = break (== ']') ('[':s)
                     in unwords ((f ++ "]" ++ qual) : take 2 (words r))
                _ -> s
  where qual | th   = " [TH]"  -- what's this?
             | True = ""

junk :: String -> Bool
junk s = any (`isPrefixOf` s) junkPre || any (`isInfixOf` s) junkIn
 where junkPre = [ "In order, the following would be installed:"
                 , "ld: warning: could not create compact unwind for"
                 , "Loading package"
                 , "Resolving dependencies"
                 , "Building source dist"
                 , "Preprocessing library"
                 , "Preprocessing executable"
                 , "Running Haddock"
                 , "Running hscolour"
                 , "Warning: The documentation for the following packages are not installed."
                 , "links will be generated to these packages:"
                 , "haddock coverage for"
                 , "Compiling with Herbie floating point stabilization"
                 ]
       junkIn  = [ "(reinstall) changes:"
                 , "could not find link destinations for"
                 , "Could not find documentation for exported module:"
                 -- subjective
                 , "Data.SBV.BitVectors.Data.Cached Data.SBV.BitVectors.Data.SW Data.SBV.BitVectors.Data.Outputtable Data.SBV.BitVectors.Data.Quantifier"
                 , "Data.SBV.BitVectors.Data.Outputtable Data.SBV.BitVectors.STree.STreeInternal Data.SBV.SMT.SMT.SMTModel Data.SBV.SMT.SMT.SMTEngine Data.SBV.BitVectors.Data.State Data.SBV.Compilers.CodeGen.CgState"
                 ]
