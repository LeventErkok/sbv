-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Compilation of symbolic programs to C
-----------------------------------------------------------------------------

{-# LANGUAGE CPP           #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-incomplete-uni-patterns #-}

module Data.SBV.Compilers.C(compileToC, compileToCLib, compileToC', compileToCLib') where

import Control.DeepSeq                (rnf)
import Data.Char                      (isSpace)
import Data.List                      (nub, intercalate, intersperse)
import Data.Maybe                     (isJust, isNothing, fromJust)
import qualified Data.Foldable as F   (toList)
import qualified Data.Set      as Set (member, union, unions, empty, toList, singleton, fromList)
import System.FilePath                (takeBaseName, replaceExtension)
import System.Random

import Data.SBV.Core.Symbolic (ResultInp(..), ProgInfo(..))

-- Work around the fact that GHC 8.4.1 started exporting <>.. Hmm..
import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Core.Data
import Data.SBV.Compilers.CodeGen

import Data.SBV.Utils.PrettyNum   (chex, showCFloat, showCDouble)

import GHC.Stack

---------------------------------------------------------------------------
-- * API
---------------------------------------------------------------------------

-- | Given a symbolic computation, render it as an equivalent collection of files
-- that make up a C program:
--
--   * The first argument is the directory name under which the files will be saved. To save
--     files in the current directory pass @'Just' \".\"@. Use 'Nothing' for printing to stdout.
--
--   * The second argument is the name of the C function to generate.
--
--   * The final argument is the function to be compiled.
--
-- Compilation will also generate a @Makefile@,  a header file, and a driver (test) program, etc. As a
-- result, we return whatever the code-gen function returns. Most uses should simply have @()@ as
-- the return type here, but the value can be useful if you want to chain the result of
-- one compilation act to the next.
compileToC :: Maybe FilePath -> String -> SBVCodeGen a -> IO a
compileToC mbDirName nm f = do (retVal, cfg, bundle) <- compileToC' nm f
                               renderCgPgmBundle mbDirName (cfg, bundle)
                               return retVal

-- | Lower level version of 'compileToC', producing a 'CgPgmBundle'
compileToC' :: String -> SBVCodeGen a -> IO (a, CgConfig, CgPgmBundle)
compileToC' nm f = do rands <- randoms `fmap` newStdGen
                      codeGen SBVToC (defaultCgConfig { cgDriverVals = rands }) nm f

-- | Create code to generate a library archive (.a) from given symbolic functions. Useful when generating code
-- from multiple functions that work together as a library.
--
--   * The first argument is the directory name under which the files will be saved. To save
--     files in the current directory pass @'Just' \".\"@. Use 'Nothing' for printing to stdout.
--
--   * The second argument is the name of the archive to generate.
--
--   * The third argument is the list of functions to include, in the form of function-name/code pairs, similar
--     to the second and third arguments of 'compileToC', except in a list.
compileToCLib :: Maybe FilePath -> String -> [(String, SBVCodeGen a)] -> IO [a]
compileToCLib mbDirName libName comps = do (retVal, cfg, pgm) <- compileToCLib' libName comps
                                           renderCgPgmBundle mbDirName (cfg, pgm)
                                           return retVal

-- | Lower level version of 'compileToCLib', producing a 'CgPgmBundle'
compileToCLib' :: String -> [(String, SBVCodeGen a)] -> IO ([a], CgConfig, CgPgmBundle)
compileToCLib' libName comps = do resCfgBundles <- mapM (uncurry compileToC') comps
                                  let (finalCfg, finalPgm) = mergeToLib libName [(c, b) | (_, c, b) <- resCfgBundles]
                                  return ([r | (r, _, _) <- resCfgBundles], finalCfg, finalPgm)

---------------------------------------------------------------------------
-- * Implementation
---------------------------------------------------------------------------

-- token for the target language
data SBVToC = SBVToC

instance CgTarget SBVToC where
  targetName _ = "C"
  translate  _ = cgen

-- Unexpected input, or things we will probably never support
die :: String -> a
die msg = error $ "SBV->C: Unexpected: " ++ msg

-- Unsupported features, or features TBD
tbd :: String -> a
tbd msg = error $ "SBV->C: Not yet supported: " ++ msg

cgen :: CgConfig -> String -> CgState -> Result -> CgPgmBundle
cgen cfg nm st sbvProg
   -- we rnf the main pg and the sig to make sure any exceptions in type conversion pop-out early enough
   -- this is purely cosmetic, of course..
   = rnf (render sig) `seq` rnf (render (vcat body)) `seq` result
  where result = CgPgmBundle bundleKind
                        $ filt [ ("Makefile",  (CgMakefile flags, [genMake (cgGenDriver cfg) nm nmd flags]))
                               , (nm  ++ ".h", (CgHeader [sig],   [genHeader bundleKind nm [sig] extProtos]))
                               , (nmd ++ ".c", (CgDriver,         genDriver cfg randVals nm ins outs mbRet))
                               , (nm  ++ ".c", (CgSource,         body))
                               ]

        (body, flagsNeeded) = genCProg cfg nm sig sbvProg ins outs mbRet extDecls

        bundleKind = (cgInteger cfg, cgReal cfg)

        randVals = cgDriverVals cfg

        filt xs  = [c | c@(_, (k, _)) <- xs, need k]
          where need k | isCgDriver   k = cgGenDriver cfg
                       | isCgMakefile k = cgGenMakefile cfg
                       | True           = True

        nmd      = nm ++ "_driver"
        sig      = pprCFunHeader nm ins outs mbRet
        ins      = cgInputs st
        outs     = cgOutputs st
        mbRet    = case cgReturns st of
                     []           -> Nothing
                     [CgAtomic o] -> Just o
                     [CgArray _]  -> tbd "Non-atomic return values"
                     _            -> tbd "Multiple return values"
        extProtos = case cgPrototypes st of
                     [] -> empty
                     xs -> vcat $ text "/* User given prototypes: */" : map text xs
        extDecls  = case cgDecls st of
                     [] -> empty
                     xs -> vcat $ text "/* User given declarations: */" : map text xs
        flags    = flagsNeeded ++ cgLDFlags st

-- | Pretty print a functions type. If there is only one output, we compile it
-- as a function that returns that value. Otherwise, we compile it as a void function
-- that takes return values as pointers to be updated.
pprCFunHeader :: String -> [(String, CgVal)] -> [(String, CgVal)] -> Maybe SV -> Doc
pprCFunHeader fn ins outs mbRet = retType <+> text fn P.<> parens (fsep (punctuate comma (map mkParam ins ++ map mkPParam outs)))
  where retType = case mbRet of
                   Nothing -> text "void"
                   Just sv -> pprCWord False sv

mkParam, mkPParam :: (String, CgVal) -> Doc
mkParam  (n, CgAtomic sv)     = pprCWord True  sv <+> text n
mkParam  (_, CgArray  [])     = die "mkParam: CgArray with no elements!"
mkParam  (n, CgArray  (sv:_)) = pprCWord True  sv <+> text "*" P.<> text n
mkPParam (n, CgAtomic sv)     = pprCWord False sv <+> text "*" P.<> text n
mkPParam (_, CgArray  [])     = die "mPkParam: CgArray with no elements!"
mkPParam (n, CgArray  (sv:_)) = pprCWord False sv <+> text "*" P.<> text n

-- | Renders as "const SWord8 s0", etc. the first parameter is the width of the typefield
declSV :: Int -> SV -> Doc
declSV w sv = text "const" <+> pad (showCType sv) <+> text (show sv)
  where pad s = text $ s ++ replicate (w - length s) ' '

-- | Return the proper declaration and the result as a pair. No consts
declSVNoConst :: Int -> SV -> (Doc, Doc)
declSVNoConst w sv = (text "     " <+> pad (showCType sv), text (show sv))
  where pad s = text $ s ++ replicate (w - length s) ' '

-- | Renders as "s0", etc, or the corresponding constant
showSV :: CgConfig -> [(SV, CV)] -> SV -> Doc
showSV cfg consts sv
  | sv == falseSV                 = text "false"
  | sv == trueSV                  = text "true"
  | Just cv <- sv `lookup` consts = mkConst cfg cv
  | True                          = text $ show sv

-- | Words as it would map to a C word
pprCWord :: HasKind a => Bool -> a -> Doc
pprCWord cnst v = (if cnst then text "const" else empty) <+> text (showCType v)

-- | Almost a "show", but map "SWord1" to "SBool"
-- which is used for extracting one-bit words. This is OK since C's bool type
-- handles arithmetic fine, and maps nicely to our `SWord 1`. (Same isn't true for `SInt 1`, which
-- doesn't have an easy counter-part on the C side.
showCType :: HasKind a => a -> String
showCType i = case kindOf i of
                KBounded False 1 -> "SBool"
                k                -> show k

-- | The printf specifier for the type
specifier :: CgConfig -> SV -> Doc
specifier cfg sv = case kindOf sv of
                     KBool         -> spec (False, 1)
                     KBounded b i  -> spec (b, i)
                     KUnbounded    -> spec (True, fromJust (cgInteger cfg))
                     KReal         -> specF (fromJust (cgReal cfg))
                     KFloat        -> specF CgFloat
                     KDouble       -> specF CgDouble
                     KString       -> text "%s"
                     KChar         -> text "%c"
                     KRational     -> die   "rational sort"
                     KFP{}         -> die   "arbitrary float sort"
                     KList k       -> die $ "list sort: " ++ show k
                     KSet  k       -> die $ "set sort: " ++ show k
                     KUserSort s _ -> die $ "user sort: " ++ s
                     KTuple k      -> die $ "tuple sort: " ++ show k
                     KMaybe  k     -> die $ "maybe sort: "  ++ show k
                     KEither k1 k2 -> die $ "either sort: " ++ show (k1, k2)
  where u8InHex = cgShowU8InHex cfg

        spec :: (Bool, Int) -> Doc
        spec (False,  1) = text "%d"
        spec (False,  8)
          | u8InHex      = text "0x%02\"PRIx8\""
          | True         = text "%\"PRIu8\""
        spec (True,   8) = text "%\"PRId8\""
        spec (False, 16) = text "0x%04\"PRIx16\"U"
        spec (True,  16) = text "%\"PRId16\""
        spec (False, 32) = text "0x%08\"PRIx32\"UL"
        spec (True,  32) = text "%\"PRId32\"L"
        spec (False, 64) = text "0x%016\"PRIx64\"ULL"
        spec (True,  64) = text "%\"PRId64\"LL"
        spec (s, sz)     = die $ "Format specifier at type " ++ (if s then "SInt" else "SWord") ++ show sz

        specF :: CgSRealType -> Doc
        specF CgFloat      = text "%a"
        specF CgDouble     = text "%a"
        specF CgLongDouble = text "%Lf"

-- | Make a constant value of the given type. We don't check for out of bounds here, as it should not be needed.
--   There are many options here, using binary, decimal, etc. We simply use decimal for values 8-bits or less,
--   and hex otherwise.
mkConst :: CgConfig -> CV -> Doc
mkConst cfg  (CV KReal (CAlgReal (AlgRational _ r))) = double (fromRational r :: Double) P.<> sRealSuffix (fromJust (cgReal cfg))
  where sRealSuffix CgFloat      = text "F"
        sRealSuffix CgDouble     = empty
        sRealSuffix CgLongDouble = text "L"
mkConst cfg (CV KUnbounded       (CInteger i)) = showSizedConst (cgShowU8InHex cfg) i (True, fromJust (cgInteger cfg))
mkConst cfg (CV (KBounded sg sz) (CInteger i)) = showSizedConst (cgShowU8InHex cfg) i (sg,   sz)
mkConst cfg (CV KBool            (CInteger i)) = showSizedConst (cgShowU8InHex cfg) i (False, 1)
mkConst _   (CV KFloat           (CFloat f))   = text $ showCFloat f
mkConst _   (CV KDouble          (CDouble d))  = text $ showCDouble d
mkConst _   (CV KString          (CString s))  = text $ show s
mkConst _   (CV KChar            (CChar c))    = text $ show c
mkConst _   cv                                 = die $ "mkConst: " ++ show cv

showSizedConst :: Bool -> Integer -> (Bool, Int) -> Doc
showSizedConst _   i   (False,  1) = text (if i == 0 then "false" else "true")
showSizedConst u8h i t@(False,  8)
  | u8h                            = text (chex False True t i)
  | True                           = integer i
showSizedConst _   i   (True,   8) = integer i
showSizedConst _   i t@(False, 16) = text $ chex False True t i
showSizedConst _   i t@(True,  16) = text $ chex False True t i
showSizedConst _   i t@(False, 32) = text $ chex False True t i
showSizedConst _   i t@(True,  32) = text $ chex False True t i
showSizedConst _   i t@(False, 64) = text $ chex False True t i
showSizedConst _   i t@(True,  64) = text $ chex False True t i
showSizedConst _   i   (s, sz)     = die $ "Constant " ++ show i ++ " at type " ++ (if s then "SInt" else "SWord") ++ show sz

-- | Generate a makefile. The first argument is True if we have a driver.
genMake :: Bool -> String -> String -> [String] -> Doc
genMake ifdr fn dn ldFlags = foldr1 ($$) [l | (True, l) <- lns]
 where ifld = not (null ldFlags)
       ld | ifld = text "${LDFLAGS}"
          | True = empty
       lns = [ (True, text "# Makefile for" <+> nm P.<> text ". Automatically generated by SBV. Do not edit!")
             , (True, text "")
             , (True, text "# include any user-defined .mk file in the current directory.")
             , (True, text "-include *.mk")
             , (True, text "")
             , (True, text "CC?=gcc")
             , (True, text "CCFLAGS?=-Wall -O3 -DNDEBUG -fomit-frame-pointer")
             , (ifld, text "LDFLAGS?=" P.<> text (unwords ldFlags))
             , (True, text "")
             , (ifdr, text "all:" <+> nmd)
             , (ifdr, text "")
             , (True, nmo P.<> text (": " ++ ppSameLine (hsep [nmc, nmh])))
             , (True, text "\t${CC} ${CCFLAGS}" <+> text "-c $< -o $@")
             , (True, text "")
             , (ifdr, nmdo P.<> text ":" <+> nmdc)
             , (ifdr, text "\t${CC} ${CCFLAGS}" <+> text "-c $< -o $@")
             , (ifdr, text "")
             , (ifdr, nmd P.<> text (": " ++ ppSameLine (hsep [nmo, nmdo])))
             , (ifdr, text "\t${CC} ${CCFLAGS}" <+> text "$^ -o $@" <+> ld)
             , (ifdr, text "")
             , (True, text "clean:")
             , (True, text "\trm -f *.o")
             , (True, text "")
             , (ifdr, text "veryclean: clean")
             , (ifdr, text "\trm -f" <+> nmd)
             , (ifdr, text "")
             ]
       nm   = text fn
       nmd  = text dn
       nmh  = nm P.<> text ".h"
       nmc  = nm P.<> text ".c"
       nmo  = nm P.<> text ".o"
       nmdc = nmd P.<> text ".c"
       nmdo = nmd P.<> text ".o"

-- | Generate the header
genHeader :: (Maybe Int, Maybe CgSRealType) -> String -> [Doc] -> Doc -> Doc
genHeader (ik, rk) fn sigs protos =
     text "/* Header file for" <+> nm P.<> text ". Automatically generated by SBV. Do not edit! */"
  $$ text ""
  $$ text "#ifndef" <+> tag
  $$ text "#define" <+> tag
  $$ text ""
  $$ text "#include <stdio.h>"
  $$ text "#include <stdlib.h>"
  $$ text "#include <inttypes.h>"
  $$ text "#include <stdint.h>"
  $$ text "#include <stdbool.h>"
  $$ text "#include <string.h>"
  $$ text "#include <math.h>"
  $$ text ""
  $$ text "/* The boolean type */"
  $$ text "typedef bool SBool;"
  $$ text ""
  $$ text "/* The float type */"
  $$ text "typedef float SFloat;"
  $$ text ""
  $$ text "/* The double type */"
  $$ text "typedef double SDouble;"
  $$ text ""
  $$ text "/* Unsigned bit-vectors */"
  $$ text "typedef uint8_t  SWord8;"
  $$ text "typedef uint16_t SWord16;"
  $$ text "typedef uint32_t SWord32;"
  $$ text "typedef uint64_t SWord64;"
  $$ text ""
  $$ text "/* Signed bit-vectors */"
  $$ text "typedef int8_t  SInt8;"
  $$ text "typedef int16_t SInt16;"
  $$ text "typedef int32_t SInt32;"
  $$ text "typedef int64_t SInt64;"
  $$ text ""
  $$ imapping
  $$ rmapping
  $$ text ("/* Entry point prototype" ++ plu ++ ": */")
  $$ vcat (map (P.<> semi) sigs)
  $$ text ""
  $$ protos
  $$ text "#endif /*" <+> tag <+> text "*/"
  $$ text ""
 where nm  = text fn
       tag = text "__" P.<> nm P.<> text "__HEADER_INCLUDED__"
       plu = if length sigs /= 1 then "s" else ""
       imapping = case ik of
                    Nothing -> empty
                    Just i  ->    text "/* User requested mapping for SInteger.                                 */"
                               $$ text "/* NB. Loss of precision: Target type is subject to modular arithmetic. */"
                               $$ text ("typedef SInt" ++ show i ++ " SInteger;")
                               $$ text ""
       rmapping = case rk of
                    Nothing -> empty
                    Just t  ->    text "/* User requested mapping for SReal.                          */"
                               $$ text "/* NB. Loss of precision: Target type is subject to rounding. */"
                               $$ text ("typedef " ++ show t ++ " SReal;")
                               $$ text ""

sepIf :: Bool -> Doc
sepIf b = if b then text "" else empty

-- | Generate an example driver program
genDriver :: CgConfig -> [Integer] -> String -> [(String, CgVal)] -> [(String, CgVal)] -> Maybe SV -> [Doc]
genDriver cfg randVals fn inps outs mbRet = [pre, header, body, post]
 where pre    =  text "/* Example driver program for" <+> nm P.<> text ". */"
              $$ text "/* Automatically generated by SBV. Edit as you see fit! */"
              $$ text ""
              $$ text "#include <stdio.h>"
       header =  text "#include" <+> doubleQuotes (nm P.<> text ".h")
              $$ text ""
              $$ text "int main(void)"
              $$ text "{"
       body   =  text ""
              $$ nest 2 (   vcat (map mkInp pairedInputs)
                      $$ vcat (map mkOut outs)
                      $$ sepIf (not (null [() | (_, _, CgArray{}) <- pairedInputs]) || not (null outs))
                      $$ call
                      $$ text ""
                      $$ (case mbRet of
                              Just sv -> text "printf" P.<> parens (printQuotes (fcall <+> text "=" <+> specifier cfg sv P.<> text "\\n")
                                                                              P.<> comma <+> resultVar) P.<> semi
                              Nothing -> text "printf" P.<> parens (printQuotes (fcall <+> text "->\\n")) P.<> semi)
                      $$ vcat (map display outs)
                      )
       post   =   text ""
              $+$ nest 2 (text "return 0" P.<> semi)
              $$  text "}"
              $$  text ""
       nm = text fn
       pairedInputs = matchRands randVals inps
       matchRands _      []                                 = []
       matchRands []     _                                  = die "Run out of driver values!"
       matchRands (r:rs) ((n, CgAtomic sv)            : cs) = ([mkRVal sv r], n, CgAtomic sv) : matchRands rs cs
       matchRands _      ((n, CgArray [])             : _ ) = die $ "Unsupported empty array input " ++ show n
       matchRands rs     ((n, a@(CgArray sws@(sv:_))) : cs)
          | length frs /= l                                 = die "Run out of driver values!"
          | True                                            = (map (mkRVal sv) frs, n, a) : matchRands srs cs
          where l          = length sws
                (frs, srs) = splitAt l rs
       mkRVal sv r = mkConst cfg $ mkConstCV (kindOf sv) r
       mkInp (_,  _, CgAtomic{})         = empty  -- constant, no need to declare
       mkInp (_,  n, CgArray [])         = die $ "Unsupported empty array value for " ++ show n
       mkInp (vs, n, CgArray sws@(sv:_)) =  pprCWord True sv <+> text n P.<> brackets (int (length sws)) <+> text "= {"
                                                      $$ nest 4 (fsep (punctuate comma (align vs)))
                                                      $$ text "};"
                                         $$ text ""
                                         $$ text "printf" P.<> parens (printQuotes (text "Contents of input array" <+> text n P.<> text ":\\n")) P.<> semi
                                         $$ display (n, CgArray sws)
                                         $$ text ""
       mkOut (v, CgAtomic sv)            = pprCWord False sv <+> text v P.<> semi
       mkOut (v, CgArray [])             = die $ "Unsupported empty array value for " ++ show v
       mkOut (v, CgArray sws@(sv:_))     = pprCWord False sv <+> text v P.<> brackets (int (length sws)) P.<> semi
       resultVar = text "__result"
       call = case mbRet of
                Nothing -> fcall P.<> semi
                Just sv -> pprCWord True sv <+> resultVar <+> text "=" <+> fcall P.<> semi
       fcall = nm P.<> parens (fsep (punctuate comma (map mkCVal pairedInputs ++ map mkOVal outs)))
       mkCVal ([v], _, CgAtomic{}) = v
       mkCVal (vs,  n, CgAtomic{}) = die $ "Unexpected driver value computed for " ++ show n ++ render (hcat vs)
       mkCVal (_,   n, CgArray{})  = text n
       mkOVal (n, CgAtomic{})      = text "&" P.<> text n
       mkOVal (n, CgArray{})       = text n
       display (n, CgAtomic sv)         = text "printf" P.<> parens (printQuotes (text " " <+> text n <+> text "=" <+> specifier cfg sv
                                                                                P.<> text "\\n") P.<> comma <+> text n) P.<> semi
       display (n, CgArray [])         =  die $ "Unsupported empty array value for " ++ show n
       display (n, CgArray sws@(sv:_)) =   text "int" <+> nctr P.<> semi
                                        $$ text "for(" P.<> nctr <+> text "= 0;" <+> nctr <+> text "<" <+> int len <+> text "; ++" P.<> nctr P.<> text ")"
                                        $$ nest 2 (text "printf" P.<> parens (printQuotes (text " " <+> entrySpec <+> text "=" <+> spec P.<> text "\\n")
                                                                 P.<> comma <+> nctr <+> comma P.<> entry) P.<> semi)
                  where nctr      = text n P.<> text "_ctr"
                        entry     = text n P.<> text "[" P.<> nctr P.<> text "]"
                        entrySpec = text n P.<> text "[%" P.<> int tab P.<> text "d]"
                        spec      = specifier cfg sv
                        len       = length sws
                        tab       = length $ show (len - 1)

-- | Generate the C program
genCProg :: CgConfig -> String -> Doc -> Result -> [(String, CgVal)] -> [(String, CgVal)] -> Maybe SV -> Doc -> ([Doc], [String])
genCProg cfg fn proto (Result pinfo kindInfo _tvals _ovals cgs topInps (_, preConsts) tbls arrs _uis axioms (SBVPgm asgns) cstrs origAsserts _) inVars outVars mbRet extDecls
  | isNothing (cgInteger cfg) && KUnbounded `Set.member` kindInfo
  = error $ "SBV->C: Unbounded integers are not supported by the C compiler."
          ++ "\nUse 'cgIntegerSize' to specify a fixed size for SInteger representation."
  | KString `Set.member` kindInfo
  = notyet "Strings"
  | KChar `Set.member` kindInfo
  = notyet "Characters"
  | any isSet kindInfo
  = notyet "Sets (SSet)"
  | any isList kindInfo
  = notyet "Lists (SList)"
  | any isTuple kindInfo
  = notyet "Tuples (STupleN)"
  | any isMaybe kindInfo
  = notyet "Optional (SMaybe) values"
  | any isEither kindInfo
  = notyet "Either (SEither) values"
  | isNothing (cgReal cfg) && KReal `Set.member` kindInfo
  = error $ "SBV->C: SReal values are not supported by the C compiler."
          ++ "\nUse 'cgSRealType' to specify a custom type for SReal representation."
  | not (null unsupportedBVs)
  = error $ "SBV->C: Unsupported bit-vector type(s): " ++ intercalate ", " (map show unsupportedBVs)
  | not (null usorts)
  = error $ "SBV->C: Cannot compile functions with uninterpreted sorts: " ++ intercalate ", " usorts
  | hasQuants pinfo
  = error "SBV->C: Cannot compile in the presence of quantified variables."
  | not $ null (progSpecialRels pinfo)
  = error "SBV->C: Cannot compile in the presence of special relations."
  | not (null axioms)
  = error "SBV->C: Cannot compile in the presence of 'smtFunction' definitions, use 'compileToCLib' instead."
  | not (null cstrs)
  = tbd "Explicit constraints"
  | not (null arrs)
  = tbd "User specified arrays"
  | True
  = ([pre, header, post], flagsNeeded)
 where notyet m = error $ "SBV->C: " ++ m ++ " are currently not supported by the C compiler. Please get in touch if you'd like support for this feature!"

       asserts | cgIgnoreAsserts cfg = []
               | True                = origAsserts

       usorts = [s | KUserSort s _ <- Set.toList kindInfo, s /= "RoundingMode"] -- No support for any sorts other than RoundingMode!

       pre    =  text "/* File:" <+> doubleQuotes (nm P.<> text ".c") P.<> text ". Automatically generated by SBV. Do not edit! */"
              $$ text ""

       header = text "#include" <+> doubleQuotes (nm P.<> text ".h")

       unsupportedBVs = [k | k@(KBounded sg sz) <- Set.toList kindInfo, (not . supported) (sg, sz)]
         where supported (False, sz) = sz `elem` [1, 8, 16, 32, 64]
               supported (True,  sz) = sz `elem` [   8, 16, 32, 64]

       post   = text ""
             $$ vcat (map codeSeg cgs)
             $$ extDecls
             $$ proto
             $$ text "{"
             $$ text ""
             $$ nest 2 (   vcat (concatMap (genIO True . (\v -> (isAlive v, v))) inVars)
                        $$ vcat (merge (map genTbl tbls) (map genAsgn assignments) (map genAssert asserts))
                        $$ sepIf (not (null assignments) || not (null tbls))
                        $$ vcat (concatMap (genIO False . (True,)) outVars)
                        $$ maybe empty mkRet mbRet
                       )
             $$ text "}"
             $$ text ""

       nm = text fn

       assignments = F.toList asgns

       -- Do we need any linker flags for C?
       flagsNeeded = nub $ concatMap (getLDFlag . opRes) assignments
          where opRes (sv, SBVApp o _) = (o, kindOf sv)

       codeSeg (fnm, ls) =  text "/* User specified custom code for" <+> doubleQuotes (text fnm) <+> text "*/"
                         $$ vcat (map text ls)
                         $$ text ""

       ins = case topInps of
               ResultTopInps (is, []) -> is
               ResultTopInps is       -> die $ "Unexpected trackers: " ++ show is
               ResultLamInps is       -> die $ "Unexpected inputs  : " ++ show is

       typeWidth = getMax 0 $ [len (kindOf s) | (s, _) <- assignments] ++ [len (kindOf s) | NamedSymVar s _ <- ins]
                where len KReal{}            = 5
                      len KFloat{}           = 6 -- SFloat
                      len KDouble{}          = 7 -- SDouble
                      len KString{}          = 7 -- SString
                      len KChar{}            = 5 -- SChar
                      len KUnbounded{}       = 8
                      len KBool              = 5 -- SBool
                      len (KBounded False n) = 5 + length (show n) -- SWordN
                      len (KBounded True  n) = 4 + length (show n) -- SIntN
                      len KRational{}        = die   "Rational."
                      len KFP{}              = die   "Arbitrary float."
                      len (KList s)          = die $ "List sort: " ++ show s
                      len (KSet  s)          = die $ "Set sort: " ++ show s
                      len (KTuple s)         = die $ "Tuple sort: " ++ show s
                      len (KMaybe k)         = die $ "Maybe sort: " ++ show k
                      len (KEither k1 k2)    = die $ "Either sort: " ++ show (k1, k2)
                      len (KUserSort s _)    = die $ "Uninterpreted sort: " ++ s

                      getMax 8 _      = 8  -- 8 is the max we can get with SInteger, so don't bother looking any further
                      getMax m []     = m
                      getMax m (x:xs) = getMax (m `max` x) xs

       consts = (falseSV, falseCV) : (trueSV, trueCV) : preConsts

       isConst s = isJust (lookup s consts)

       -- TODO: The following is brittle. We should really have a function elsewhere
       -- that walks the SBVExprs and collects the SWs together.
       usedVariables = Set.unions (retSWs : map usedCgVal outVars ++ map usedAsgn assignments)
         where retSWs = maybe Set.empty Set.singleton mbRet

               usedCgVal (_, CgAtomic s)  = Set.singleton s
               usedCgVal (_, CgArray ss)  = Set.fromList ss
               usedAsgn  (_, SBVApp o ss) = Set.union (opSWs o) (Set.fromList ss)

               opSWs (LkUp _ a b)             = Set.fromList [a, b]
               opSWs (IEEEFP (FP_Cast _ _ s)) = Set.singleton s
               opSWs _                        = Set.empty

       isAlive :: (String, CgVal) -> Bool
       isAlive (_, CgAtomic sv) = sv `Set.member` usedVariables
       isAlive (_, _)           = True

       genIO :: Bool -> (Bool, (String, CgVal)) -> [Doc]
       genIO True  (alive, (cNm, CgAtomic sv)) = [declSV typeWidth sv  <+> text "=" <+> text cNm P.<> semi               | alive]
       genIO False (alive, (cNm, CgAtomic sv)) = [text "*" P.<> text cNm <+> text "=" <+> showSV cfg consts sv P.<> semi | alive]
       genIO isInp (_,     (cNm, CgArray sws)) = zipWith genElt sws [(0::Int)..]
         where genElt sv i
                 | isInp = declSV typeWidth sv <+> text "=" <+> text entry       P.<> semi
                 | True  = text entry          <+> text "=" <+> showSV cfg consts sv P.<> semi
                 where entry = cNm ++ "[" ++ show i ++ "]"

       mkRet sv = text "return" <+> showSV cfg consts sv P.<> semi

       genTbl :: ((Int, Kind, Kind), [SV]) -> (Int, Doc)
       genTbl ((i, _, k), elts) =  (location, static <+> text "const" <+> text (show k) <+> text ("table" ++ show i) P.<> text "[] = {"
                                              $$ nest 4 (fsep (punctuate comma (align (map (showSV cfg consts) elts))))
                                              $$ text "};")
         where static   = if location == -1 then text "static" else empty
               location = maximum (-1 : map getNodeId elts)

       getNodeId s@(SV _ (NodeId (_, _, n))) | isConst s = -1
                                             | True      = n

       genAsgn :: (SV, SBVExpr) -> (Int, Doc)
       genAsgn (sv, n) = (getNodeId sv, ppExpr cfg consts n (declSV typeWidth sv) (declSVNoConst typeWidth sv) P.<> semi)

       -- merge tables intermixed with assignments and assertions, paying attention to putting tables as
       -- early as possible and tables right after.. Note that the assignment list (second argument) is sorted on its order
       merge :: [(Int, Doc)] -> [(Int, Doc)] -> [(Int, Doc)] -> [Doc]
       merge tables asgnments asrts = map snd $ merge2 asrts (merge2 tables asgnments)
         where merge2 []               as                  = as
               merge2 ts               []                  = ts
               merge2 ts@((i, t):trest) as@((i', a):arest)
                 | i < i'                                 = (i,  t)  : merge2 trest as
                 | True                                   = (i', a) : merge2 ts arest

       genAssert (msg, cs, sv) = (getNodeId sv, doc)
         where doc =     text "/* ASSERTION:" <+> text msg
                     $$  maybe empty (vcat . map text) (locInfo (getCallStack `fmap` cs))
                     $$  text " */"
                     $$  text "if" P.<> parens (showSV cfg consts sv)
                     $$  text "{"
                     $+$ nest 2 (vcat [errOut, text "exit(-1);"])
                     $$  text "}"
                     $$  text ""
               errOut = text $ "fprintf(stderr, \"%s:%d:ASSERTION FAILED: " ++ msg ++ "\\n\", __FILE__, __LINE__);"
               locInfo (Just ps) = let loc (f, sl) = concat [srcLocFile sl, ":", show (srcLocStartLine sl), ":", show (srcLocStartCol sl), ":", f ]
                                   in case map loc ps of
                                         []     -> Nothing
                                         (f:rs) -> Just $ (" * SOURCE   : " ++ f) : map (" *            " ++)  rs
               locInfo _         = Nothing

handlePB :: PBOp -> [Doc] -> Doc
handlePB o args = case o of
                    PB_AtMost  k -> addIf (repeat 1) <+> text "<=" <+> int k
                    PB_AtLeast k -> addIf (repeat 1) <+> text ">=" <+> int k
                    PB_Exactly k -> addIf (repeat 1) <+> text "==" <+> int k
                    PB_Le cs   k -> addIf cs         <+> text "<=" <+> int k
                    PB_Ge cs   k -> addIf cs         <+> text ">=" <+> int k
                    PB_Eq cs   k -> addIf cs         <+> text "==" <+> int k

  where addIf :: [Int] -> Doc
        addIf cs = parens $ fsep $ intersperse (text "+") [parens (a <+> text "?" <+> int c <+> text ":" <+> int 0) | (a, c) <- zip args cs]

handleIEEE :: FPOp -> [(SV, CV)] -> [(SV, Doc)] -> Doc -> Doc
handleIEEE w consts as var = cvt w
  where same f                   = (f, f)
        named fnm dnm f          = (f fnm, f dnm)

        cvt (FP_Cast from to m)     = case checkRM (m `lookup` consts) of
                                        Nothing          -> cast $ \[a] -> parens (text (show to)) <+> rnd a
                                        Just (Left  msg) -> die msg
                                        Just (Right msg) -> tbd msg
                                      where -- if we're converting from float to some integral like; first use rint/rintf to do the internal conversion and then cast.
                                            rnd a
                                             | (isFloat from || isDouble from) && (isBounded to || isUnbounded to)
                                             = let f = if isFloat from then "rintf" else "rint"
                                               in text f P.<> parens a
                                             | True
                                             = a

        cvt (FP_Reinterpret f t) = case (f, t) of
                                     (KBounded False 32, KFloat)  -> cast $ cpy "sizeof(SFloat)"
                                     (KBounded False 64, KDouble) -> cast $ cpy "sizeof(SDouble)"
                                     (KFloat,  KBounded False 32) -> cast $ cpy "sizeof(SWord32)"
                                     (KDouble, KBounded False 64) -> cast $ cpy "sizeof(SWord64)"
                                     _                            -> die $ "Reinterpretation from : " ++ show f ++ " to " ++ show t
                                    where cpy sz = \[a] -> let alhs = text "&" P.<> var
                                                               arhs = text "&" P.<> a
                                                           in text "memcpy" P.<> parens (fsep (punctuate comma [alhs, arhs, text sz]))
        cvt FP_Abs               = dispatch $ named "fabsf" "fabs" $ \nm _ [a] -> text nm P.<> parens a
        cvt FP_Neg               = dispatch $ same $ \_ [a] -> text "-" P.<> a
        cvt FP_Add               = dispatch $ same $ \_ [a, b] -> a <+> text "+" <+> b
        cvt FP_Sub               = dispatch $ same $ \_ [a, b] -> a <+> text "-" <+> b
        cvt FP_Mul               = dispatch $ same $ \_ [a, b] -> a <+> text "*" <+> b
        cvt FP_Div               = dispatch $ same $ \_ [a, b] -> a <+> text "/" <+> b
        cvt FP_FMA               = dispatch $ named "fmaf"  "fma"  $ \nm _ [a, b, c] -> text nm P.<> parens (fsep (punctuate comma [a, b, c]))
        cvt FP_Sqrt              = dispatch $ named "sqrtf" "sqrt" $ \nm _ [a]       -> text nm P.<> parens a
        cvt FP_Rem               = dispatch $ named "fmodf" "fmod" $ \nm _ [a, b]    -> text nm P.<> parens (fsep (punctuate comma [a, b]))
        cvt FP_RoundToIntegral   = dispatch $ named "rintf" "rint" $ \nm _ [a]       -> text nm P.<> parens a
        cvt FP_Min               = dispatch $ named "fminf" "fmin" $ \nm k [a, b]    -> wrapMinMax k a b (text nm P.<> parens (fsep (punctuate comma [a, b])))
        cvt FP_Max               = dispatch $ named "fmaxf" "fmax" $ \nm k [a, b]    -> wrapMinMax k a b (text nm P.<> parens (fsep (punctuate comma [a, b])))
        cvt FP_ObjEqual          = let mkIte   x y z = x <+> text "?" <+> y <+> text ":" <+> z
                                       chkNaN  x     = text "isnan"   P.<> parens x
                                       signbit x     = text "signbit" P.<> parens x
                                       eq      x y   = parens (x <+> text "==" <+> y)
                                       eqZero  x     = eq x (text "0")
                                       negZero x     = parens (signbit x <+> text "&&" <+> eqZero x)
                                   in dispatch $ same $ \_ [a, b] -> mkIte (chkNaN a) (chkNaN b) (mkIte (negZero a) (negZero b) (mkIte (negZero b) (negZero a) (eq a b)))
        cvt FP_IsNormal          = dispatch $ same $ \_ [a] -> text "isnormal" P.<> parens a
        cvt FP_IsSubnormal       = dispatch $ same $ \_ [a] -> text "FP_SUBNORMAL == fpclassify" P.<> parens a
        cvt FP_IsZero            = dispatch $ same $ \_ [a] -> text "FP_ZERO == fpclassify" P.<> parens a
        cvt FP_IsInfinite        = dispatch $ same $ \_ [a] -> text "isinf" P.<> parens a
        cvt FP_IsNaN             = dispatch $ same $ \_ [a] -> text "isnan" P.<> parens a
        cvt FP_IsNegative        = dispatch $ same $ \_ [a] -> text "!isnan" P.<> parens a <+> text "&&" <+> text "signbit"  P.<> parens a
        cvt FP_IsPositive        = dispatch $ same $ \_ [a] -> text "!isnan" P.<> parens a <+> text "&&" <+> text "!signbit" P.<> parens a

        -- grab the rounding-mode, if present, and make sure it's RoundNearestTiesToEven. Otherwise skip.
        fpArgs = case as of
                   []            -> []
                   ((m, _):args) -> case kindOf m of
                                      KUserSort "RoundingMode" _ -> case checkRM (m `lookup` consts) of
                                                                      Nothing          -> args
                                                                      Just (Left  msg) -> die msg
                                                                      Just (Right msg) -> tbd msg
                                      _                          -> as

        -- Check that the RM is RoundNearestTiesToEven.
        -- If we start supporting other rounding-modes, this would be the point where we'd insert the rounding-mode set/reset code
        -- instead of merely returning OK or not
        checkRM (Just cv@(CV (KUserSort "RoundingMode" _) v)) =
              case v of
                CUserSort (_, "RoundNearestTiesToEven") -> Nothing
                CUserSort (_, s)                        -> Just (Right $ "handleIEEE: Unsupported rounding-mode: " ++ show s ++ " for: " ++ show w)
                _                                       -> Just (Left  $ "handleIEEE: Unexpected value for rounding-mode: " ++ show cv ++ " for: " ++ show w)
        checkRM (Just cv) = Just (Left  $ "handleIEEE: Expected rounding-mode, but got: " ++ show cv ++ " for: " ++ show w)
        checkRM Nothing   = Just (Right $ "handleIEEE: Non-constant rounding-mode for: " ++ show w)

        pickOp _          []             = die $ "Cannot determine float/double kind for op: " ++ show w
        pickOp (fOp, dOp) args@((a,_):_) = case kindOf a of
                                             KFloat  -> fOp KFloat  (map snd args)
                                             KDouble -> dOp KDouble (map snd args)
                                             k       -> die $ "handleIEEE: Expected double/float args, but got: " ++ show k ++ " for: " ++ show w

        dispatch (fOp, dOp) = pickOp (fOp, dOp) fpArgs
        cast f              = f (map snd fpArgs)

        -- In SMT-Lib, fpMin/fpMax is underspecified when given +0/-0 as the two arguments. (In any order.)
        -- In C, the second argument is returned. (I think, might depend on the architecture, optimizations etc.).
        -- We'll translate it so that we deterministically return +0.
        -- There's really no good choice here.
        wrapMinMax k a b s = parens cond <+> text "?" <+> zero <+> text ":" <+> s
          where zero = text $ if k == KFloat then showCFloat 0 else showCDouble 0
                cond =                   parens (text "FP_ZERO == fpclassify" P.<> parens a)                                      -- a is zero
                       <+> text "&&" <+> parens (text "FP_ZERO == fpclassify" P.<> parens b)                                      -- b is zero
                       <+> text "&&" <+> parens (text "signbit" P.<> parens a <+> text "!=" <+> text "signbit" P.<> parens b)       -- a and b differ in sign

ppExpr :: CgConfig -> [(SV, CV)] -> SBVExpr -> Doc -> (Doc, Doc) -> Doc
ppExpr cfg consts (SBVApp op opArgs) lhs (typ, var)
  | doNotAssign op
  = typ <+> var P.<> semi <+> rhs
  | True
  = lhs <+> text "=" <+> rhs
  where doNotAssign (IEEEFP FP_Reinterpret{}) = True   -- generates a memcpy instead; no simple assignment
        doNotAssign _                         = False  -- generates simple assignment

        rhs = p op (map (showSV cfg consts) opArgs)

        rtc = cgRTC cfg

        cBinOps = [ (Plus, "+"),  (Times, "*"), (Minus, "-")
                  , (Equal, "=="), (NotEqual, "!="), (LessThan, "<"), (GreaterThan, ">"), (LessEq, "<="), (GreaterEq, ">=")
                  , (And, "&"), (Or, "|"), (XOr, "^")
                  ]

        -- see if we can find a constant shift; makes the output way more readable
        getShiftAmnt def [_, sv] = case sv `lookup` consts of
                                    Just (CV _  (CInteger i)) -> integer i
                                    _                         -> def
        getShiftAmnt def _       = def

        hd _ (h:_) = h
        hd w []    = error $ "Data.SBV.C.ppExpr: Impossible happened: " ++ w ++ ", received empty list!"

        p :: Op -> [Doc] -> Doc
        p (ArrRead _)       _  = tbd "User specified arrays (ArrRead)"
        p (ArrEq _ _)       _  = tbd "User specified arrays (ArrEq)"
        p (Label s)        [a] = a <+> text "/*" <+> text s <+> text "*/"
        p (IEEEFP w)         as = handleIEEE w  consts (zip opArgs as) var
        p (PseudoBoolean pb) as = handlePB pb as
        p (OverflowOp o) _      = tbd $ "Overflow operations" ++ show o
        p (KindCast _ to)   [a] = parens (text (show to)) <+> a
        p (Uninterpreted s) [] = text "/* Uninterpreted constant */" <+> text s
        p (Uninterpreted s) as = text "/* Uninterpreted function */" <+> text s P.<> parens (fsep (punctuate comma as))
        p (Extract i j) [a]    = extract i j (hd "Extract" opArgs) a
        p Join [a, b]          = join (let (s1 : s2 : _) = opArgs in (s1, s2, a, b))
        p (Rol i) [a]          = rotate True  i a (hd "Rol" opArgs)
        p (Ror i) [a]          = rotate False i a (hd "Ror" opArgs)
        p Shl     [a, i]       = shift  True  (getShiftAmnt i opArgs) a -- The order of i/a being reversed here is
        p Shr     [a, i]       = shift  False (getShiftAmnt i opArgs) a -- intentional and historical (from the days when Shl/Shr had a constant parameter.)
        p Not [a]              = case kindOf (hd "Not" opArgs) of
                                   -- be careful about booleans, bitwise complement is not correct for them!
                                   KBool -> text "!" P.<> a
                                   _     -> text "~" P.<> a
        p Ite [a, b, c] = a <+> text "?" <+> b <+> text ":" <+> c
        p (LkUp (t, k, _, len) ind def) []
          | not rtc                    = lkUp -- ignore run-time-checks per user request
          | needsCheckL && needsCheckR = cndLkUp checkBoth
          | needsCheckL                = cndLkUp checkLeft
          | needsCheckR                = cndLkUp checkRight
          | True                       = lkUp
          where [index, defVal] = map (showSV cfg consts) [ind, def]

                lkUp = text "table" P.<> int t P.<> brackets (showSV cfg consts ind)
                cndLkUp cnd = cnd <+> text "?" <+> defVal <+> text ":" <+> lkUp

                checkLeft  = index <+> text "< 0"
                checkRight = index <+> text ">=" <+> int len
                checkBoth  = parens (checkLeft <+> text "||" <+> checkRight)

                canOverflow True  sz = (2::Integer)^(sz-1)-1 >= fromIntegral len
                canOverflow False sz = (2::Integer)^sz    -1 >= fromIntegral len

                (needsCheckL, needsCheckR) = case k of
                                               KBool           -> (False, canOverflow False (1::Int))
                                               KBounded sg sz  -> (sg, canOverflow sg sz)
                                               KReal           -> die "array index with real value"
                                               KFloat          -> die "array index with float value"
                                               KDouble         -> die "array index with double value"
                                               KFP{}           -> die "array index with arbitrary float value"
                                               KRational       -> die "array index with rational value"
                                               KString         -> die "array index with string value"
                                               KChar           -> die "array index with character value"
                                               KUnbounded      -> case cgInteger cfg of
                                                                    Nothing -> (True, True) -- won't matter, it'll be rejected later
                                                                    Just i  -> (True, canOverflow True i)
                                               KList     s     -> die $ "List sort " ++ show s
                                               KSet      s     -> die $ "Set sort " ++ show s
                                               KTuple    s     -> die $ "Tuple sort " ++ show s
                                               KMaybe    ek    -> die $ "Maybe sort " ++ show ek
                                               KEither   k1 k2 -> die $ "Either sort " ++ show (k1, k2)
                                               KUserSort s _   -> die $ "Uninterpreted sort: " ++ s

        -- Div/Rem should be careful on 0, in the SBV world x `div` 0 is 0, x `rem` 0 is x
        -- NB: Quot is supposed to truncate toward 0; Not clear to me if C guarantees this behavior.
        -- Brief googling suggests C99 does indeed truncate toward 0, but other C compilers might differ.
        p Quot [a, b] = let k = kindOf (hd "Quot" opArgs)
                            z = mkConst cfg $ mkConstCV k (0::Integer)
                        in protectDiv0 k "/" z a b
        p Rem  [a, b] = protectDiv0 (kindOf (hd "Rem" opArgs)) "%" a a b
        p UNeg [a]    = parens (text "-" <+> a)
        p Abs  [a]    = let f KFloat             = text "fabsf" P.<> parens a
                            f KDouble            = text "fabs"  P.<> parens a
                            f (KBounded False _) = text "/* unsigned, skipping call to abs */" <+> a
                            f (KBounded True 32) = text "labs"  P.<> parens a
                            f (KBounded True 64) = text "llabs" P.<> parens a
                            f KUnbounded         = case cgInteger cfg of
                                                     Nothing -> f $ KBounded True 32 -- won't matter, it'll be rejected later
                                                     Just i  -> f $ KBounded True i
                            f KReal              = case cgReal cfg of
                                                     Nothing           -> f KDouble -- won't matter, it'll be rejected later
                                                     Just CgFloat      -> f KFloat
                                                     Just CgDouble     -> f KDouble
                                                     Just CgLongDouble -> text "fabsl" P.<> parens a
                            f _                  = text "abs" P.<> parens a
                        in f (kindOf (hd "Abs" opArgs))
        -- for And/Or, translate to boolean versions if on boolean kind
        p And [a, b] | kindOf (hd "And" opArgs) == KBool = a <+> text "&&" <+> b
        p Or  [a, b] | kindOf (hd "Or"  opArgs) == KBool = a <+> text "||" <+> b
        p o [a, b]
          | Just co <- lookup o cBinOps
          = a <+> text co <+> b

        p Implies [a, b] | kindOf (hd "Implies" opArgs) == KBool = parens (text "!" P.<> a <+> text "||" <+> b)

        p NotEqual xs = mkDistinct xs
        p o args = die $ "Received operator " ++ show o ++ " applied to " ++ show args

        -- generate a pairwise inequality check
        mkDistinct args = fsep $ andAll $ walk args
          where walk []     = []
                walk (e:es) = map (pair e) es ++ walk es

                pair e1 e2  = parens (e1 <+> text "!=" <+> e2)

                -- like punctuate, but more spacing
                andAll []     = []
                andAll (d:ds) = go d ds
                     where go d' [] = [d']
                           go d' (e:es) = (d' <+> text "&&") : go e es

        -- Div0 needs to protect, but only when the arguments are not float/double. (Div by 0 for those are well defined to be Inf/NaN etc.)
        protectDiv0 k divOp def a b = case k of
                                        KFloat  -> res
                                        KDouble -> res
                                        _       -> wrap
           where res  = a <+> text divOp <+> b
                 wrap = parens (b <+> text "== 0") <+> text "?" <+> def <+> text ":" <+> parens res

        shift toLeft i a = a <+> text cop <+> i
          where cop | toLeft = "<<"
                    | True   = ">>"

        rotate toLeft i a s
          | i < 0   = rotate (not toLeft) (-i) a s
          | i == 0  = a
          | True    = case kindOf s of
                        KBounded True _             -> tbd $ "Rotation of signed quantities: " ++ show (toLeft, i, s)
                        KBounded False sz | i >= sz -> rotate toLeft (i `mod` sz) a s
                        KBounded False sz           ->     parens (a <+> text cop  <+> int i)
                                                      <+> text "|"
                                                      <+> parens (a <+> text cop' <+> int (sz - i))
                        KUnbounded                  -> shift toLeft (int i) a -- For SInteger, rotate is the same as shift in Haskell
                        _                           -> tbd $ "Rotation for unbounded quantity: " ++ show (toLeft, i, s)
          where (cop, cop') | toLeft = ("<<", ">>")
                            | True   = (">>", "<<")

        -- TBD: below we only support the values for extract that are "easy" to implement. These should cover
        -- almost all instances actually generated by SBV, however.
        extract hi lo i a  -- Isolate the bit-extraction case
          | hi == lo, KBounded _ sz <- kindOf i, hi < sz, hi >= 0
          = if hi == 0
            then text "(SBool)" <+> parens (a <+> text "& 1")
            else text "(SBool)" <+> parens (parens (a <+> text ">>" <+> int hi) <+> text "& 1")
        extract hi lo i a
          | srcSize `notElem` [64, 32, 16]
          = bad "Unsupported source size"
          | (hi + 1) `mod` 8 /= 0 || lo `mod` 8 /= 0
          = bad "Unsupported non-byte-aligned extraction"
          | tgtSize < 8 || tgtSize `mod` 8 /= 0
          = bad "Unsupported target size"
          | True
          = text cast <+> shifted
          where bad why    = tbd $ "extract with " ++ show (hi, lo, k, i) ++ " (Reason: " ++ why ++ ".)"

                k          = kindOf i
                srcSize    = intSizeOf k
                tgtSize    = hi - lo + 1
                signChange = srcSize == tgtSize

                cast
                  | signChange && hasSign k = "(SWord" ++ show srcSize ++ ")"
                  | signChange              = "(SInt"  ++ show srcSize ++ ")"
                  | True                    = "(SWord" ++ show tgtSize ++ ")"

                shifted
                  | lo == 0 = a
                  | True    = parens (a <+> text ">>" <+> int lo)

        -- TBD: ditto here for join, just like extract above
        join (i, j, a, b) = case (kindOf i, kindOf j) of
                              (KBounded False  8, KBounded False  8) -> parens (parens (text "(SWord16)" <+> a) <+> text "<< 8")  <+> text "|" <+> parens (text "(SWord16)" <+> b)
                              (KBounded False 16, KBounded False 16) -> parens (parens (text "(SWord32)" <+> a) <+> text "<< 16") <+> text "|" <+> parens (text "(SWord32)" <+> b)
                              (KBounded False 32, KBounded False 32) -> parens (parens (text "(SWord64)" <+> a) <+> text "<< 32") <+> text "|" <+> parens (text "(SWord64)" <+> b)
                              (k1,                k2)                -> tbd $ "join with " ++ show ((k1, i), (k2, j))

-- same as doubleQuotes, except we have to make sure there are no line breaks..
-- Otherwise breaks the generated code.. sigh
printQuotes :: Doc -> Doc
printQuotes d = text $ '"' : ppSameLine d ++ "\""

-- Remove newlines.. Useful when generating Makefile and such
ppSameLine :: Doc -> String
ppSameLine = trim . render
 where trim ""        = ""
       trim ('\n':cs) = ' ' : trim (dropWhile isSpace cs)
       trim (c:cs)    = c   : trim cs

-- Align a bunch of docs to occupy the exact same length by padding in the left by space
-- this is ugly and inefficient, but easy to code..
align :: [Doc] -> [Doc]
align ds = map (text . pad) ss
  where ss    = map render ds
        l     = maximum (0 : map length ss)
        pad s = replicate (l - length s) ' ' ++ s

-- | Merge a bunch of bundles to generate code for a library. For the final
-- config, we simply return the first config we receive, or the default if none.
mergeToLib :: String -> [(CgConfig, CgPgmBundle)] -> (CgConfig, CgPgmBundle)
mergeToLib libName cfgBundles
  | length nubKinds /= 1
  = error $  "Cannot merge programs with differing SInteger/SReal mappings. Received the following kinds:\n"
          ++ unlines (map show nubKinds)
  | True
  = (finalCfg, CgPgmBundle bundleKind $ sources ++ libHeader : [libDriver | anyDriver] ++ [libMake | anyMake])
  where bundles     = map snd cfgBundles
        kinds       = [k | CgPgmBundle k _ <- bundles]
        nubKinds    = nub kinds
        bundleKind  = case nubKinds of
                        bk:_ -> bk
                        []   -> error "Data.SBV.C: Impossible happened: mergeLibs: kinds ended up being empty!"
        files       = concat [fs | CgPgmBundle _ fs <- bundles]
        sigs        = concat [ss | (_, (CgHeader ss, _)) <- files]
        anyMake     = not (null [() | (_, (CgMakefile{}, _)) <- files])
        drivers     = [ds | (_, (CgDriver, ds)) <- files]
        anyDriver   = not (null drivers)
        mkFlags     = nub (concat [xs | (_, (CgMakefile xs, _)) <- files])
        sources     = [(f, (CgSource, [pre, libHInclude, post])) | (f, (CgSource, [pre, _, post])) <- files]
        sourceNms   = map fst sources
        libHeader   = (libName ++ ".h", (CgHeader sigs, [genHeader bundleKind libName sigs empty]))
        libHInclude = text "#include" <+> text (show (libName ++ ".h"))
        libMake     = ("Makefile", (CgMakefile mkFlags, [genLibMake anyDriver libName sourceNms mkFlags]))
        libDriver   = (libName ++ "_driver.c", (CgDriver, mergeDrivers libName libHInclude (zip (map takeBaseName sourceNms) drivers)))
        finalCfg    = case cfgBundles of
                        []         -> defaultCgConfig
                        ((c, _):_) -> c

-- | Create a Makefile for the library
genLibMake :: Bool -> String -> [String] -> [String] -> Doc
genLibMake ifdr libName fs ldFlags = foldr1 ($$) [l | (True, l) <- lns]
 where ifld = not (null ldFlags)
       ld | ifld = text "${LDFLAGS}"
          | True = empty
       lns = [ (True, text "# Makefile for" <+> nm P.<> text ". Automatically generated by SBV. Do not edit!")
             , (True,  text "")
             , (True,  text "# include any user-defined .mk file in the current directory.")
             , (True,  text "-include *.mk")
             , (True,  text "")
             , (True,  text "CC?=gcc")
             , (True,  text "CCFLAGS?=-Wall -O3 -DNDEBUG -fomit-frame-pointer")
             , (ifld,  text "LDFLAGS?=" P.<> text (unwords ldFlags))
             , (True,  text "AR?=ar")
             , (True,  text "ARFLAGS?=cr")
             , (True,  text "")
             , (not ifdr,  text ("all: " ++ liba))
             , (ifdr,      text ("all: " ++ unwords [liba, libd]))
             , (True,  text "")
             , (True,  text liba P.<> text (": " ++ unwords os))
             , (True,  text "\t${AR} ${ARFLAGS} $@ $^")
             , (True,  text "")
             , (ifdr,  text libd P.<> text (": " ++ unwords [libd ++ ".c", libh]))
             , (ifdr,  text ("\t${CC} ${CCFLAGS} $< -o $@ " ++ liba) <+> ld)
             , (ifdr,  text "")
             , (True,  vcat (zipWith mkObj os fs))
             , (True,  text "clean:")
             , (True,  text "\trm -f *.o")
             , (True,  text "")
             , (True,  text "veryclean: clean")
             , (not ifdr,  text "\trm -f" <+> text liba)
             , (ifdr,      text "\trm -f" <+> text (unwords [liba, libd]))
             , (True,  text "")
             ]
       nm = text libName
       liba = libName ++ ".a"
       libh = libName ++ ".h"
       libd = libName ++ "_driver"
       os   = map (`replaceExtension` ".o") fs
       mkObj o f =  text o P.<> text (": " ++ unwords [f, libh])
                 $$ text "\t${CC} ${CCFLAGS} -c $< -o $@"
                 $$ text ""

-- | Create a driver for a library
mergeDrivers :: String -> Doc -> [(FilePath, [Doc])] -> [Doc]
mergeDrivers libName inc ds = pre : concatMap mkDFun ds ++ [callDrivers (map fst ds)]
  where pre =  text "/* Example driver program for" <+> text libName P.<> text ". */"
            $$ text "/* Automatically generated by SBV. Edit as you see fit! */"
            $$ text ""
            $$ text "#include <stdio.h>"
            $$ inc
        mkDFun (f, [_pre, _header, body, _post]) = [header, body, post]
           where header =  text ""
                        $$ text ("void " ++ f ++ "_driver(void)")
                        $$ text "{"
                 post   =  text "}"
        mkDFun (f, _) = die $ "mergeDrivers: non-conforming driver program for " ++ show f
        callDrivers fs =   text ""
                       $$  text "int main(void)"
                       $$  text "{"
                       $+$ nest 2 (vcat (map call fs))
                       $$  nest 2 (text "return 0;")
                       $$  text "}"
        call f =  text psep
               $$ text ptag
               $$ text psep
               $$ text (f ++ "_driver();")
               $$ text ""
           where tag  = "** Driver run for " ++ f ++ ":"
                 ptag = "printf(\"" ++ tag ++ "\\n\");"
                 lsep = replicate (length tag) '='
                 psep = "printf(\"" ++ lsep ++ "\\n\");"

-- Does this operation with this result kind require an LD flag?
getLDFlag :: (Op, Kind) -> [String]
getLDFlag (o, k) = flag o
  where math = ["-lm"]

        flag (IEEEFP FP_Cast{})                                     = math
        flag (IEEEFP fop)       | fop `elem` requiresMath           = math
        flag Abs                | k `elem` [KFloat, KDouble, KReal] = math
        flag _                                                      = []

        requiresMath = [ FP_Abs
                       , FP_FMA
                       , FP_Sqrt
                       , FP_Rem
                       , FP_Min
                       , FP_Max
                       , FP_RoundToIntegral
                       , FP_ObjEqual
                       , FP_IsSubnormal
                       , FP_IsInfinite
                       , FP_IsNaN
                       , FP_IsNegative
                       , FP_IsPositive
                       , FP_IsNormal
                       , FP_IsZero
                       ]

{- HLint ignore module "Redundant lambda" -}
