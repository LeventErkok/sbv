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

{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Data.SBV.Compilers.CodeGen where

import Control.Monad.Trans
import Control.Monad.State.Lazy
import Data.Char (toLower)
import Data.List (nub, isPrefixOf, intersperse, (\\))
import System.Directory (createDirectory, doesDirectoryExist, doesFileExist)
import System.FilePath ((</>))
import Text.PrettyPrint.HughesPJ (Doc, render)

import Data.SBV.BitVectors.Data

-- | Abstract over code generation for different languages
class CgTarget a where
  targetName :: a -> String
  translate  :: a -> Bool -> [Integer] -> String -> CgState -> Result -> CgPgmBundle

-- | Options for code-generation.
data CgConfig = CgConfig {
          cgRTC        :: Bool          -- ^ If 'True', perform run-time-checks for index-out-of-bounds or shifting-by-large values etc.
        , cgDriverVals :: [Integer]     -- ^ Values to use for the driver program generated, useful for generating non-random drivers.
        }

-- | Default options for code generation. The run-time checks are turned-off, and the driver values are completely random.
defaultCgConfig :: CgConfig
defaultCgConfig = CgConfig { cgRTC = False, cgDriverVals = [] }

-- | Abstraction of target language values
data CgVal = CgAtomic SW
           | CgArray  [SW]

data CgState = CgState {
          cgInputs       :: [(String, CgVal)]
        , cgOutputs      :: [(String, CgVal)]
        , cgReturns      :: [CgVal]
        }

initCgState :: CgState
initCgState = CgState {
          cgInputs       = []
        , cgOutputs      = []
        , cgReturns      = []
        }

newtype SBVCodeGen a = SBVCodeGen (StateT CgState Symbolic a)
                   deriving (Monad, MonadIO, MonadState CgState)

-- Reach into symbolic monad..
liftSymbolic :: Symbolic a -> SBVCodeGen a
liftSymbolic = SBVCodeGen . lift

-- Reach into symbolic monad and output a value. Returns the corresponding SW
cgSBVToSW :: SBV a -> SBVCodeGen SW
cgSBVToSW = liftSymbolic . sbvToSymSW

-- | Creates an atomic input in the generated code.
cgInput :: (HasSignAndSize a, SymWord a) => String -> SBVCodeGen (SBV a)
cgInput nm = do r <- liftSymbolic free_
                sw <- cgSBVToSW r
                modify (\s -> s { cgInputs = (nm, CgAtomic sw) : cgInputs s })
                return r

-- | Creates an array input in the generated code.
cgInputArr :: (HasSignAndSize a, SymWord a) => Int -> String -> SBVCodeGen [SBV a]
cgInputArr sz nm
  | sz < 1 = error $ "SBV.cgInputArr: Array inputs must have at least one element, given " ++ show sz ++ " for " ++ show nm
  | True   = do rs <- liftSymbolic $ (mapM (const free_) [1..sz])
                sws <- mapM cgSBVToSW rs
                modify (\s -> s { cgInputs = (nm, CgArray sws) : cgInputs s })
                return rs

-- | Creates an atomic output in the generated code.
cgOutput :: (HasSignAndSize a, SymWord a) => String -> SBV a -> SBVCodeGen ()
cgOutput nm v = do _ <- liftSymbolic (output v)
                   sw <- cgSBVToSW v
                   modify (\s -> s { cgOutputs = (nm, CgAtomic sw) : cgOutputs s })

-- | Creates an array output in the generated code.
cgOutputArr :: (HasSignAndSize a, SymWord a) => String -> [SBV a] -> SBVCodeGen ()
cgOutputArr nm vs
  | sz < 1 = error $ "SBV.cgOutputArr: Array outputs must have at least one element, received " ++ show sz ++ " for " ++ show nm
  | True   = do _ <- liftSymbolic (mapM output vs)
                sws <- mapM cgSBVToSW vs
                modify (\s -> s { cgOutputs = (nm, CgArray sws) : cgOutputs s })
  where sz = length vs

-- | Creates a returned (unnamed) value in the generated code.
cgReturn :: (HasSignAndSize a, SymWord a) => SBV a -> SBVCodeGen ()
cgReturn v = do _ <- liftSymbolic (output v)
                sw <- cgSBVToSW v
                modify (\s -> s { cgReturns = CgAtomic sw : cgReturns s })

-- | Creates a returned (unnamed) array value in the generated code.
cgReturnArr :: (HasSignAndSize a, SymWord a) => [SBV a] -> SBVCodeGen ()
cgReturnArr vs
  | sz < 1 = error $ "SBV.cgReturnArr: Array returns must have at least one element, received " ++ show sz
  | True   = do _ <- liftSymbolic (mapM output vs)
                sws <- mapM cgSBVToSW vs
                modify (\s -> s { cgReturns = CgArray sws : cgReturns s })
  where sz = length vs

-- | Representation of a collection of generated programs. Code generation
-- produces a number of files (drivers, source, headers, etc.) and corresponding
-- contents.
newtype CgPgmBundle = CgPgmBundle [(FilePath, Doc)]

instance Show CgPgmBundle where
   show (CgPgmBundle fs) = concat $ intersperse "\n" $ map showFile fs

showFile :: (FilePath, Doc) -> String
showFile (f, d) =  "== BEGIN: " ++ show f ++ " ================\n"
                ++ render d
                ++ "== END: " ++ show f ++ " =================="

codeGen' :: CgTarget l => l -> CgConfig -> String -> SBVCodeGen () -> IO CgPgmBundle
codeGen' l cgConfig nm (SBVCodeGen comp) = do
   (((), st'), res) <- runSymbolic' $ runStateT comp initCgState
   let st = st' { cgInputs       = reverse (cgInputs st')
                , cgOutputs      = reverse (cgOutputs st')
                }
       allNamedVars = map fst (cgInputs st ++ cgOutputs st)
       dupNames = allNamedVars \\ nub allNamedVars
   when (not (null dupNames)) $ do
        error $ "SBV.codeGen: The following input/output names are duplicated: " ++ unwords dupNames
   return $ translate l (cgRTC cgConfig) (cgDriverVals cgConfig) nm st res

codeGen :: CgTarget l => l -> CgConfig -> String -> Maybe FilePath -> SBVCodeGen () -> IO ()
codeGen l cgConfig nm mbDirName comp = do
   putStrLn $ "Compiling " ++ show nm ++ " to " ++ targetName l ++ ".."
   CgPgmBundle files <- codeGen' l cgConfig nm comp
   goOn <- maybe (return True) (check files) mbDirName
   if goOn then do mapM_ (renderFile mbDirName) files
                   putStrLn "Done."
           else putStrLn "Aborting."
  where createOutDir :: FilePath -> IO ()
        createOutDir dn = do b <- doesDirectoryExist dn
                             when (not b) $ do putStrLn $ "Creating directory " ++ show dn ++ ".."
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
renderFile Nothing  fp     = putStrLn $ showFile fp
