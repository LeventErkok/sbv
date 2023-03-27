-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.CodeGen
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Code generation utilities
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                        #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.CodeGen (
        -- * The codegen monad
          SBVCodeGen(..), cgSym

        -- * Specifying inputs, SBV variants
        , cgInput,  cgInputArr
        , cgOutput, cgOutputArr
        , cgReturn, cgReturnArr

        -- * Specifying inputs, SVal variants
        , svCgInput,  svCgInputArr
        , svCgOutput, svCgOutputArr
        , svCgReturn, svCgReturnArr

        -- * Settings
        , cgPerformRTCs, cgSetDriverValues
        , cgAddPrototype, cgAddDecl, cgAddLDFlags, cgIgnoreSAssert, cgOverwriteFiles, cgShowU8UsingHex
        , cgIntegerSize, cgSRealType, CgSRealType(..)

        -- * Infrastructure
        , CgTarget(..), CgConfig(..), CgState(..), CgPgmBundle(..), CgPgmKind(..), CgVal(..)
        , defaultCgConfig, initCgState, isCgDriver, isCgMakefile

        -- * Generating collateral
        , cgGenerateDriver, cgGenerateMakefile, codeGen, renderCgPgmBundle
        ) where

import Control.Monad             (filterM, replicateM, unless)
import Control.Monad.Trans       (MonadIO(liftIO), lift)
import Control.Monad.State.Lazy  (MonadState, StateT(..), modify')
import Data.Char                 (toLower, isSpace)
import Data.List                 (nub, isPrefixOf, intercalate, (\\))
import System.Directory          (createDirectoryIfMissing, doesDirectoryExist, doesFileExist)
import System.FilePath           ((</>))
import System.IO                 (hFlush, stdout)

import           Text.PrettyPrint.HughesPJ      (Doc, vcat)
import qualified Text.PrettyPrint.HughesPJ as P (render)

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic (MonadSymbolic(..), svToSymSV, svMkSymVar, outputSVal, VarContext(..))

import Data.SBV.Provers.Prover(defaultSMTCfg)

#if MIN_VERSION_base(4,11,0)
import Control.Monad.Fail as Fail
#endif

-- | Abstract over code generation for different languages
class CgTarget a where
  targetName :: a -> String
  translate  :: a -> CgConfig -> String -> CgState -> Result -> CgPgmBundle

-- | Options for code-generation.
data CgConfig = CgConfig {
          cgRTC                :: Bool               -- ^ If 'True', perform run-time-checks for index-out-of-bounds or shifting-by-large values etc.
        , cgInteger            :: Maybe Int          -- ^ Bit-size to use for representing SInteger (if any)
        , cgReal               :: Maybe CgSRealType  -- ^ Type to use for representing SReal (if any)
        , cgDriverVals         :: [Integer]          -- ^ Values to use for the driver program generated, useful for generating non-random drivers.
        , cgGenDriver          :: Bool               -- ^ If 'True', will generate a driver program
        , cgGenMakefile        :: Bool               -- ^ If 'True', will generate a makefile
        , cgIgnoreAsserts      :: Bool               -- ^ If 'True', will ignore 'Data.SBV.sAssert' calls
        , cgOverwriteGenerated :: Bool               -- ^ If 'True', will overwrite the generated files without prompting.
        , cgShowU8InHex        :: Bool               -- ^ If 'True', then 8-bit unsigned values will be shown in hex as well, otherwise decimal. (Other types always shown in hex.)
        }

-- | Default options for code generation. The run-time checks are turned-off, and the driver values are completely random.
defaultCgConfig :: CgConfig
defaultCgConfig = CgConfig { cgRTC                = False
                           , cgInteger            = Nothing
                           , cgReal               = Nothing
                           , cgDriverVals         = []
                           , cgGenDriver          = True
                           , cgGenMakefile        = True
                           , cgIgnoreAsserts      = False
                           , cgOverwriteGenerated = False
                           , cgShowU8InHex        = False
                           }

-- | Abstraction of target language values
data CgVal = CgAtomic SV
           | CgArray  [SV]

-- | Code-generation state
data CgState = CgState {
          cgInputs         :: [(String, CgVal)]
        , cgOutputs        :: [(String, CgVal)]
        , cgReturns        :: [CgVal]
        , cgPrototypes     :: [String]    -- extra stuff that goes into the header
        , cgDecls          :: [String]    -- extra stuff that goes into the top of the file
        , cgLDFlags        :: [String]    -- extra options that go to the linker
        , cgFinalConfig    :: CgConfig
        }

-- | Initial configuration for code-generation
initCgState :: CgState
initCgState = CgState {
          cgInputs         = []
        , cgOutputs        = []
        , cgReturns        = []
        , cgPrototypes     = []
        , cgDecls          = []
        , cgLDFlags        = []
        , cgFinalConfig    = defaultCgConfig
        }

-- | The code-generation monad. Allows for precise layout of input values
-- reference parameters (for returning composite values in languages such as C),
-- and return values.
newtype SBVCodeGen a = SBVCodeGen (StateT CgState Symbolic a)
                   deriving ( Applicative, Functor, Monad, MonadIO, MonadState CgState
                            , MonadSymbolic
#if MIN_VERSION_base(4,11,0)
                            , Fail.MonadFail
#endif
                            )

-- | Reach into symbolic monad from code-generation
cgSym :: Symbolic a -> SBVCodeGen a
cgSym = SBVCodeGen . lift

-- | Sets RTC (run-time-checks) for index-out-of-bounds, shift-with-large value etc. on/off. Default: 'False'.
cgPerformRTCs :: Bool -> SBVCodeGen ()
cgPerformRTCs b = modify' (\s -> s { cgFinalConfig = (cgFinalConfig s) { cgRTC = b } })

-- | Sets number of bits to be used for representing the 'SInteger' type in the generated C code.
-- The argument must be one of @8@, @16@, @32@, or @64@. Note that this is essentially unsafe as
-- the semantics of unbounded Haskell integers becomes reduced to the corresponding bit size, as
-- typical in most C implementations.
cgIntegerSize :: Int -> SBVCodeGen ()
cgIntegerSize i
  | i `notElem` [8, 16, 32, 64]
  = error $ "SBV.cgIntegerSize: Argument must be one of 8, 16, 32, or 64. Received: " ++ show i
  | True
  = modify' (\s -> s { cgFinalConfig = (cgFinalConfig s) { cgInteger = Just i }})

-- | Possible mappings for the 'SReal' type when translated to C. Used in conjunction
-- with the function 'cgSRealType'. Note that the particular characteristics of the
-- mapped types depend on the platform and the compiler used for compiling the generated
-- C program. See <http://en.wikipedia.org/wiki/C_data_types> for details.
data CgSRealType = CgFloat      -- ^ @float@
                 | CgDouble     -- ^ @double@
                 | CgLongDouble -- ^ @long double@
                 deriving Eq

-- 'Show' instance for 'cgSRealType' displays values as they would be used in a C program
instance Show CgSRealType where
  show CgFloat      = "float"
  show CgDouble     = "double"
  show CgLongDouble = "long double"

-- | Sets the C type to be used for representing the 'SReal' type in the generated C code.
-- The setting can be one of C's @"float"@, @"double"@, or @"long double"@, types, depending
-- on the precision needed. Note that this is essentially unsafe as the semantics of
-- infinite precision SReal values becomes reduced to the corresponding floating point type in
-- C, and hence it is subject to rounding errors.
cgSRealType :: CgSRealType -> SBVCodeGen ()
cgSRealType rt = modify' (\s -> s {cgFinalConfig = (cgFinalConfig s) { cgReal = Just rt }})

-- | Should we generate a driver program? Default: 'True'. When a library is generated, it will have
-- a driver if any of the constituent functions has a driver. (See 'Data.SBV.Tools.CodeGen.compileToCLib'.)
cgGenerateDriver :: Bool -> SBVCodeGen ()
cgGenerateDriver b = modify' (\s -> s { cgFinalConfig = (cgFinalConfig s) { cgGenDriver = b } })

-- | Should we generate a Makefile? Default: 'True'.
cgGenerateMakefile :: Bool -> SBVCodeGen ()
cgGenerateMakefile b = modify' (\s -> s { cgFinalConfig = (cgFinalConfig s) { cgGenMakefile = b } })

-- | Sets driver program run time values, useful for generating programs with fixed drivers for testing. Default: None, i.e., use random values.
cgSetDriverValues :: [Integer] -> SBVCodeGen ()
cgSetDriverValues vs = modify' (\s -> s { cgFinalConfig = (cgFinalConfig s) { cgDriverVals = vs } })

-- | Ignore assertions (those generated by 'Data.SBV.sAssert' calls) in the generated C code
cgIgnoreSAssert :: Bool -> SBVCodeGen ()
cgIgnoreSAssert b = modify' (\s -> s { cgFinalConfig = (cgFinalConfig s) { cgIgnoreAsserts = b } })

-- | Adds the given lines to the header file generated, useful for generating programs with uninterpreted functions.
cgAddPrototype :: [String] -> SBVCodeGen ()
cgAddPrototype ss = modify' (\s -> let old = cgPrototypes s
                                       new = if null old then ss else old ++ [""] ++ ss
                                   in s { cgPrototypes = new })

-- | If passed 'True', then we will not ask the user if we're overwriting files as we generate
-- the C code. Otherwise, we'll prompt.
cgOverwriteFiles :: Bool -> SBVCodeGen ()
cgOverwriteFiles b = modify' (\s -> s { cgFinalConfig = (cgFinalConfig s) { cgOverwriteGenerated = b } })

-- | If passed 'True', then we will show 'SWord 8' type in hex. Otherwise we'll show it in decimal. All signed
-- types are shown decimal, and all unsigned larger types are shown hexadecimal otherwise.
cgShowU8UsingHex :: Bool -> SBVCodeGen ()
cgShowU8UsingHex b = modify' (\s -> s { cgFinalConfig = (cgFinalConfig s) { cgShowU8InHex = b } })


-- | Adds the given lines to the program file generated, useful for generating programs with uninterpreted functions.
cgAddDecl :: [String] -> SBVCodeGen ()
cgAddDecl ss = modify' (\s -> s { cgDecls = cgDecls s ++ ss })

-- | Adds the given words to the compiler options in the generated Makefile, useful for linking extra stuff in.
cgAddLDFlags :: [String] -> SBVCodeGen ()
cgAddLDFlags ss = modify' (\s -> s { cgLDFlags = cgLDFlags s ++ ss })

-- | Creates an atomic input in the generated code.
svCgInput :: Kind -> String -> SBVCodeGen SVal
svCgInput k nm = do r  <- symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just ALL)) k Nothing
                    sv <- svToSymSV r
                    modify' (\s -> s { cgInputs = (nm, CgAtomic sv) : cgInputs s })
                    return r

-- | Creates an array input in the generated code.
svCgInputArr :: Kind -> Int -> String -> SBVCodeGen [SVal]
svCgInputArr k sz nm
  | sz < 1 = error $ "SBV.cgInputArr: Array inputs must have at least one element, given " ++ show sz ++ " for " ++ show nm
  | True   = do rs  <- symbolicEnv >>= liftIO . replicateM sz . svMkSymVar (NonQueryVar (Just ALL)) k Nothing
                sws <- mapM svToSymSV rs
                modify' (\s -> s { cgInputs = (nm, CgArray sws) : cgInputs s })
                return rs

-- | Creates an atomic output in the generated code.
svCgOutput :: String -> SVal -> SBVCodeGen ()
svCgOutput nm v = do _ <- outputSVal v
                     sv <- svToSymSV v
                     modify' (\s -> s { cgOutputs = (nm, CgAtomic sv) : cgOutputs s })

-- | Creates an array output in the generated code.
svCgOutputArr :: String -> [SVal] -> SBVCodeGen ()
svCgOutputArr nm vs
  | sz < 1 = error $ "SBV.cgOutputArr: Array outputs must have at least one element, received " ++ show sz ++ " for " ++ show nm
  | True   = do mapM_ outputSVal vs
                sws <- mapM svToSymSV vs
                modify' (\s -> s { cgOutputs = (nm, CgArray sws) : cgOutputs s })
  where sz = length vs

-- | Creates a returned (unnamed) value in the generated code.
svCgReturn :: SVal -> SBVCodeGen ()
svCgReturn v = do _ <- outputSVal v
                  sv <- svToSymSV v
                  modify' (\s -> s { cgReturns = CgAtomic sv : cgReturns s })

-- | Creates a returned (unnamed) array value in the generated code.
svCgReturnArr :: [SVal] -> SBVCodeGen ()
svCgReturnArr vs
  | sz < 1 = error $ "SBV.cgReturnArr: Array returns must have at least one element, received " ++ show sz
  | True   = do mapM_ outputSVal vs
                sws <- mapM svToSymSV vs
                modify' (\s -> s { cgReturns = CgArray sws : cgReturns s })
  where sz = length vs

-- | Creates an atomic input in the generated code.
cgInput :: SymVal a => String -> SBVCodeGen (SBV a)
cgInput nm = do r  <- free_
                sv <- sbvToSymSV r
                modify' (\s -> s { cgInputs = (nm, CgAtomic sv) : cgInputs s })
                return r

-- | Creates an array input in the generated code.
cgInputArr :: SymVal a => Int -> String -> SBVCodeGen [SBV a]
cgInputArr sz nm
  | sz < 1 = error $ "SBV.cgInputArr: Array inputs must have at least one element, given " ++ show sz ++ " for " ++ show nm
  | True   = do rs <- mapM (const free_) [1..sz]
                sws <- mapM sbvToSymSV rs
                modify' (\s -> s { cgInputs = (nm, CgArray sws) : cgInputs s })
                return rs

-- | Creates an atomic output in the generated code.
cgOutput :: String -> SBV a -> SBVCodeGen ()
cgOutput nm v = do _ <- output v
                   sv <- sbvToSymSV v
                   modify' (\s -> s { cgOutputs = (nm, CgAtomic sv) : cgOutputs s })

-- | Creates an array output in the generated code.
cgOutputArr :: SymVal a => String -> [SBV a] -> SBVCodeGen ()
cgOutputArr nm vs
  | sz < 1 = error $ "SBV.cgOutputArr: Array outputs must have at least one element, received " ++ show sz ++ " for " ++ show nm
  | True   = do mapM_ output vs
                sws <- mapM sbvToSymSV vs
                modify' (\s -> s { cgOutputs = (nm, CgArray sws) : cgOutputs s })
  where sz = length vs

-- | Creates a returned (unnamed) value in the generated code.
cgReturn :: SBV a -> SBVCodeGen ()
cgReturn v = do _ <- output v
                sv <- sbvToSymSV v
                modify' (\s -> s { cgReturns = CgAtomic sv : cgReturns s })

-- | Creates a returned (unnamed) array value in the generated code.
cgReturnArr :: SymVal a => [SBV a] -> SBVCodeGen ()
cgReturnArr vs
  | sz < 1 = error $ "SBV.cgReturnArr: Array returns must have at least one element, received " ++ show sz
  | True   = do mapM_ output vs
                sws <- mapM sbvToSymSV vs
                modify' (\s -> s { cgReturns = CgArray sws : cgReturns s })
  where sz = length vs

-- | Representation of a collection of generated programs.
data CgPgmBundle = CgPgmBundle (Maybe Int, Maybe CgSRealType) [(FilePath, (CgPgmKind, [Doc]))]

-- | Different kinds of "files" we can produce. Currently this is quite "C" specific.
data CgPgmKind = CgMakefile [String]  -- list of flags to pass to linker
               | CgHeader [Doc]
               | CgSource
               | CgDriver

-- | Is this a driver program?
isCgDriver :: CgPgmKind -> Bool
isCgDriver CgDriver = True
isCgDriver _        = False

-- | Is this a make file?
isCgMakefile :: CgPgmKind -> Bool
isCgMakefile CgMakefile{} = True
isCgMakefile _            = False

-- A simple way to print bundles, mostly for debugging purposes.
instance Show CgPgmBundle where
   show (CgPgmBundle _ fs) = intercalate "\n" $ map showFile fs
    where showFile :: (FilePath, (CgPgmKind, [Doc])) -> String
          showFile (f, (_, ds)) =  "== BEGIN: " ++ show f ++ " ================\n"
                                ++ render' (vcat ds)
                                ++ "== END: " ++ show f ++ " =================="

-- | Generate code for a symbolic program, returning a Code-gen bundle, i.e., collection
-- of makefiles, source code, headers, etc.
codeGen :: CgTarget l => l -> CgConfig -> String -> SBVCodeGen a -> IO (a, CgConfig, CgPgmBundle)
codeGen l cgConfig nm (SBVCodeGen comp) = do
   ((retVal, st'), res) <- runSymbolic defaultSMTCfg CodeGen $ runStateT comp initCgState { cgFinalConfig = cgConfig }
   let st = st' { cgInputs  = reverse (cgInputs st')
                , cgOutputs = reverse (cgOutputs st')
                }
       allNamedVars = map fst (cgInputs st ++ cgOutputs st)
       dupNames = allNamedVars \\ nub allNamedVars
   unless (null dupNames) $
        error $ "SBV.codeGen: " ++ show nm ++ " has following argument names duplicated: " ++ unwords dupNames

   return (retVal, cgFinalConfig st, translate l (cgFinalConfig st) nm st res)

-- | Render a code-gen bundle to a directory or to stdout
renderCgPgmBundle :: Maybe FilePath -> (CgConfig, CgPgmBundle) -> IO ()
renderCgPgmBundle Nothing        (_  , bundle)              = print bundle
renderCgPgmBundle (Just dirName) (cfg, CgPgmBundle _ files) = do

        b <- doesDirectoryExist dirName
        unless b $ do unless overWrite $ putStrLn $ "Creating directory " ++ show dirName ++ ".."
                      createDirectoryIfMissing True dirName

        dups <- filterM (\fn -> doesFileExist (dirName </> fn)) (map fst files)

        goOn <- case (overWrite, dups) of
                  (True, _) -> return True
                  (_,   []) -> return True
                  _         -> do putStrLn $ "Code generation would overwrite the following " ++ (if length dups == 1 then "file:" else "files:")
                                  mapM_ (\fn -> putStrLn ('\t' : fn)) dups
                                  putStr "Continue? [yn] "
                                  hFlush stdout
                                  resp <- getLine
                                  return $ map toLower resp `isPrefixOf` "yes"

        if goOn then do mapM_ renderFile files
                        unless overWrite $ putStrLn "Done."
                else putStrLn "Aborting."

  where overWrite = cgOverwriteGenerated cfg

        renderFile (f, (_, ds)) = do let fn = dirName </> f
                                     unless overWrite $ putStrLn $ "Generating: " ++ show fn ++ ".."
                                     writeFile fn (render' (vcat ds))

-- | An alternative to Pretty's @render@, which might have "leading" white-space in empty lines. This version
-- eliminates such whitespace.
render' :: Doc -> String
render' = unlines . map clean . lines . P.render
  where clean x | all isSpace x = ""
                | True          = x
