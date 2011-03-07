-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Compilers.CodeGen
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Code generation utilities
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances #-}

module Data.SBV.Compilers.CodeGen where

import Data.Char (toLower)
import Data.List (isPrefixOf)
import Control.Monad (when, filterM)
import System.Directory (createDirectory, doesDirectoryExist, doesFileExist)
import System.FilePath ((</>))
import Text.PrettyPrint.HughesPJ (Doc, render)

import Data.SBV.BitVectors.Data (Outputtable(..), runSymbolic', Symbolic, Result, SymWord(..), SBV(..))

codeGen :: (SBVTarget l, CgArgs a, Outputtable b) => l -> Maybe FilePath -> String -> [String] -> (a -> b) -> IO ()
codeGen l mbDirName nm args f = do
   putStrLn $ "Compiling " ++ nm ++ " to " ++ targetName l ++ ".."
   (extraNames, res) <- runSymbolic' $ do (extras, arg) <- cgArgs args
                                          _ <- output $ f arg
                                          return extras
   let files = translate l nm extraNames res
   goOn <- maybe (return True) (check files) mbDirName
   if goOn then do mapM_ (renderFile mbDirName) files
                   putStrLn "Done."
           else putStrLn "Aborting."
  where createOutDir :: FilePath -> IO ()
        createOutDir dn = do b <- doesDirectoryExist dn
                             when (not b) $ do putStrLn $ "Creating directory " ++ show dn
                                               createDirectory dn
        check files dn = do createOutDir dn
                            dups <- filterM (\fn -> doesFileExist (dn </> fn)) (map fst files)
                            case dups of
                              [] -> return True
                              _  -> do putStrLn $ "Code generation would override the following " ++ (if length dups == 1 then "file:" else "files:")
                                       mapM_ (\fn -> putStrLn ("\t" ++ fn)) dups
                                       putStr "Continue? [yn] "
                                       resp <- getLine
                                       return $ map toLower resp `isPrefixOf` "yes"

renderFile :: Maybe FilePath -> (FilePath, Doc) -> IO ()
renderFile (Just d) (f, p) = do let fn = d </> f
                                putStrLn $ "Generating: " ++ show fn ++ ".."
                                writeFile fn (render p)
renderFile Nothing  (f, p) = do putStrLn $ "== BEGIN: " ++ show f ++ " ================"
                                putStr (render p)
                                putStrLn $ "== END: " ++ show f ++ " =================="

-- | Abstract over code generation for different languages
class SBVTarget a where
  targetName :: a -> String
  translate  :: a -> String -> [String] -> Result -> [(FilePath, Doc)]

-- | Abstract over input variables over generated functions
class CgArgs a where
   cgArgs :: [String] -> Symbolic ([String], a)

-- Single arg
instance SymWord a => CgArgs (SBV a) where
   cgArgs []     = free_  >>= \v -> return ([], v)
   cgArgs (s:ss) = free s >>= \v -> return (ss, v)

-- Tuples
instance (SymWord a, SymWord b) => CgArgs (SBV a, SBV b) where
   cgArgs ns = do (ns1, a) <- cgArgs ns
                  (ns2, b) <- cgArgs ns1
                  return (ns2, (a, b))

-- 3-Tuple
instance (SymWord a, SymWord b, SymWord c) => CgArgs (SBV a, SBV b, SBV c) where
   cgArgs ns = do (ns1, a) <- cgArgs ns
                  (ns2, b) <- cgArgs ns1
                  (ns3, c) <- cgArgs ns2
                  return (ns3, (a, b, c))

-- 4-Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d) => CgArgs (SBV a, SBV b, SBV c, SBV d) where
   cgArgs ns = do (ns1, a) <- cgArgs ns
                  (ns2, b) <- cgArgs ns1
                  (ns3, c) <- cgArgs ns2
                  (ns4, d) <- cgArgs ns3
                  return (ns4, (a, b, c, d))

-- 5-Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e) => CgArgs (SBV a, SBV b, SBV c, SBV d, SBV e) where
   cgArgs ns = do (ns1, a) <- cgArgs ns
                  (ns2, b) <- cgArgs ns1
                  (ns3, c) <- cgArgs ns2
                  (ns4, d) <- cgArgs ns3
                  (ns5, e) <- cgArgs ns4
                  return (ns5, (a, b, c, d, e))

-- 6-Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f) => CgArgs (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) where
   cgArgs ns = do (ns1, a) <- cgArgs ns
                  (ns2, b) <- cgArgs ns1
                  (ns3, c) <- cgArgs ns2
                  (ns4, d) <- cgArgs ns3
                  (ns5, e) <- cgArgs ns4
                  (ns6, f) <- cgArgs ns5
                  return (ns6, (a, b, c, d, e, f))

-- 7-Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SymWord g) => CgArgs (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) where
   cgArgs ns = do (ns1, a) <- cgArgs ns
                  (ns2, b) <- cgArgs ns1
                  (ns3, c) <- cgArgs ns2
                  (ns4, d) <- cgArgs ns3
                  (ns5, e) <- cgArgs ns4
                  (ns6, f) <- cgArgs ns5
                  (ns7, g) <- cgArgs ns6
                  return (ns7, (a, b, c, d, e, f, g))
