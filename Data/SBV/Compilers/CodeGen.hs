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

module Data.SBV.Compilers.CodeGen where

import Data.Char (toLower)
import Data.List (isPrefixOf)
import Control.Monad (when, filterM)
import System.Directory (createDirectory, doesDirectoryExist, doesFileExist)
import System.FilePath ((</>))
import Text.PrettyPrint.HughesPJ (Doc, render)

import Data.SBV.BitVectors.Data (Outputtable(..), runSymbolic, Symbolic, Result, SymWord(..), SBV(..))

codeGen :: (SBVTarget l, CgArgs a, Outputtable b) => l -> Maybe FilePath -> String -> [String] -> (a -> b) -> IO ()
codeGen l mbDirName nm args f = do
   putStrLn $ "Compiling " ++ nm ++ " to " ++ targetName l ++ ".."
   res <- runSymbolic $ cgArgs args >>= output . f
   let files = translate l nm res
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
  translate  :: a -> String -> Result -> [(FilePath, Doc)]

-- | Abstract over input variables over generated functions
class CgArgs a where
   cgArgs :: [String] -> Symbolic a

instance SymWord a => CgArgs (SBV a) where
   cgArgs []    = free_
   cgArgs (s:_) = free s
