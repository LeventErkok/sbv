-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.New
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Compilation of symbolic programs to C
-----------------------------------------------------------------------------

{-# LANGUAGE TupleSections #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-incomplete-uni-patterns #-}

module Data.SBV.Compilers.C.New(compileToC, compileToCLib, compileToC', compileToCLib') where

import Control.DeepSeq                 (rnf)
import qualified Data.ByteString       as BS
import Data.Char                       (chr, isSpace)
import qualified Data.Foldable         as F (toList)
import qualified Data.Graph            as DG
import Data.List                       (intercalate, intersperse, nub, nubBy)
import Data.Maybe                      (fromJust, fromMaybe, isJust)
import qualified Data.Set              as Set (Set, empty, fromList, insert, map, member, singleton, toList, union, unions)
import qualified Data.Text             as T
import qualified Data.Text.Encoding    as TE
import Numeric                         (showOct)
import System.FilePath                 (replaceExtension, takeBaseName)
import System.Random

import Data.SBV.Core.Symbolic (LambdaInfo(..), ResultInp(..), ProgInfo(..), SMTDef(SMTDef), smtDefInfo, smtLambdaInfo)

-- Work around the fact that GHC 8.4.1 started exporting <>.. Hmm..
import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Core.Data
import Data.SBV.Core.Kind (expandKinds, kRoundingMode)
import Data.SBV.Compilers.C.ADT
import Data.SBV.Compilers.C.Array
import Data.SBV.Compilers.C.BV
import Data.SBV.Compilers.C.FP
import Data.SBV.Compilers.C.GMP
import Data.SBV.Compilers.C.List
import Data.SBV.Compilers.C.Lowering
import Data.SBV.Compilers.C.Set
import Data.SBV.Compilers.C.Table
import Data.SBV.Compilers.C.Text
import qualified Data.SBV.Compilers.C.Types as CTypes (arrayStoredReleaseName, definedFunctionCName, elementCType, kindTag)
import Data.SBV.Compilers.C.Tuple
import Data.SBV.Compilers.C.Value (valueNeedsOwnership)
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
                               pure retVal

-- | Lower level version of 'compileToC', producing a t'CgPgmBundle'
compileToC' :: String -> SBVCodeGen a -> IO (a, CgConfig, CgPgmBundle)
compileToC' nm f = do rands <- randoms <$> newStdGen
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
                                           pure retVal

-- | Lower level version of 'compileToCLib', producing a t'CgPgmBundle'
compileToCLib' :: String -> [(String, SBVCodeGen a)] -> IO ([a], CgConfig, CgPgmBundle)
compileToCLib' libName comps = do resCfgBundles <- mapM (uncurry compileToC') comps
                                  let (finalCfg, finalPgm) = mergeToLib libName [(c, b) | (_, c, b) <- resCfgBundles]
                                  pure ([r | (r, _, _) <- resCfgBundles], finalCfg, finalPgm)

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
   -- Force type declarations, the signature, and the main program so any
   -- type-conversion exceptions appear while constructing the bundle.
   = rnf (render extraTypes) `seq` rnf (render sig) `seq` rnf (render (vcat body)) `seq` result
  where result = CgPgmBundle bundleKind
                        $ filt [ ("Makefile"   , (CgMakefile flags          , [genMake (cgGenDriver cfg) nm nmd flags]))
                               , (nm  ++ ".h"  , (CgHeader [extraTypes, sig] , [genHeader bundleKind nm [sig] extProtos extraTypes]))
                               , (nmd ++ ".c"  , (CgDriver                  , driver))
                               , (nm  ++ ".c"  , (CgSource                  , body))
                               ]

        (body, requirements) = genCProg cfg adts lists sets nm sig sbvProg ins allOuts mbRet extDecls

        bundleKind = (cgInteger cfg, cgReal cfg)

        extraTypes =  roundingModeTypeDecls usesRoundingModeType
                   $$ (if hasRequirement CRequiresWideBV then wideBVTypeDecls (wideBVKinds kinds) else empty)
                   $$ (if hasRequirement CRequiresLibBF  then arbitraryFPTypeDecls (arbitraryFPKinds kinds) else empty)
                   $$ (if hasRequirement CRequiresGMP    then gmpTypeDecls cfg kinds else empty)
                   $$ (if hasRequirement CRequiresText   then textTypeDecls kinds else empty)
                   $$ (if hasRequirement CRequiresArrays then arrayForwardTypeDecls arrays else empty)
                   $$ tupleForwardTypeDecls tuples
                   $$ adtForwardTypeDecls adts
                   $$ listForwardTypeDecls lists
                   $$ setForwardTypeDecls sets
                   $$ (if hasRequirement CRequiresLists  then listTypeDecls cfg lists else empty)
                   $$ (if hasRequirement CRequiresSets   then setTypeDecls cfg sets else empty)
                   $$ structuralTypeDecls cfg adts tuples
                   $$ adtOwnershipTypePrototypes adts
                   $$ tupleOwnershipTypeDecls cfg tuples
                   $$ adtOwnershipTypeDecls cfg adts
                   $$ (if hasRequirement CRequiresLists then listOwnershipTypeDecls cfg lists else empty)
                   $$ (if hasRequirement CRequiresSets  then setOwnershipTypeDecls cfg sets else empty)
                   $$ (if hasRequirement CRequiresArrays then arrayTypeDecls arrays else empty)
        kinds           = Set.unions [reskinds sbvProg, usedKinds]
        usedKinds       = Set.union interfaceKinds assignmentKinds
        interfaceKinds  = Set.fromList . concatMap expandKinds
                        $ concatMap cgValKinds (map snd ins ++ map snd outs ++ cgReturns st)
          where cgValKinds (CgAtomic sv) = [kindOf sv]
                cgValKinds (CgArray svs) = map kindOf svs
        assignmentKinds = Set.fromList . concatMap expandKinds $ concatMap expressionKinds assignments
          where assignments = case resAsgns sbvProg of
                                SBVPgm programAssignments -> F.toList programAssignments
                expressionKinds (resultSV, SBVApp _ arguments) = map kindOf (resultSV : arguments)
        arrays          = arrayKinds kinds
        lists           = listKinds kinds
        sets            = setKinds kinds
        adts            = adtKinds kinds usedKinds
        tuples          = tupleKinds (Set.map (resolveADTReferences adts) kinds)

        hasRequirement requirement = requirement `Set.member` requirements

        usesRoundingModeType =  any (isRoundingMode . kindOf) roundingModeValues
                             || any tableUsesRoundingMode (resTables sbvProg)
                             || any arrayUsesRoundingMode arrays
                             || any (any isRoundingMode . expandKinds) tuples
                             || any (any isRoundingMode . expandKinds) adts
          where roundingModeValues =  concatMap cgValSVs (map snd ins ++ map snd outs ++ cgReturns st)
                                   ++ roundingModeAssignments
                roundingModeAssignments = case resAsgns sbvProg of
                                            SBVPgm asgns -> [sv | (sv, _) <- F.toList asgns]
                cgValSVs (CgAtomic sv) = [sv]
                cgValSVs (CgArray svs) = svs
                tableUsesRoundingMode ((_, indexKind, resultKind), _) = isRoundingMode indexKind || isRoundingMode resultKind
                arrayUsesRoundingMode (KArray indexKind resultKind) = isRoundingMode indexKind || isRoundingMode resultKind
                arrayUsesRoundingMode _                              = False

        randVals = cgDriverVals cfg
        driver   = genDriver cfg adts randVals nm ins allOuts mbRet

        filt xs  = [c | c@(_, (k, _)) <- xs, need k]
          where need k | isCgDriver   k = cgGenDriver cfg
                       | isCgMakefile k = cgGenMakefile cfg
                       | True           = True

        nmd      = nm ++ "_driver"
        sig      = pprCFunHeader cfg nm ins allOuts mbRet
        ins      = cgInputs st
        outs     = cgOutputs st
        allOuts  = outs ++ returnOuts
        mbRet    = case cgReturns st of
                     [CgAtomic resultSV] -> Just resultSV
                     _                   -> Nothing

        returnOuts = case cgReturns st of
                       []           -> []
                       [CgAtomic{}] -> []
                       results      -> zipWith (\index returnValue -> (returnName index, returnValue)) [0 :: Int ..] results

        returnName index = availableName 0
          where availableName prefixLength
                  | candidate `elem` interfaceNames = availableName (prefixLength + 1)
                  | True                            = candidate
                  where candidate = replicate prefixLength '_' ++ "result_" ++ show index

        interfaceNames = map fst (ins ++ outs)

        extProtos = case cgPrototypes st of
                     [] -> empty
                     xs -> vcat $ text "/* User given prototypes: */" : map text xs
        extDecls  = case cgDecls st of
                     [] -> empty
                     xs -> vcat $ text "/* User given declarations: */" : map text xs
        flags    = requirementLDFlags requirements ++ cgLDFlags st

-- | Emit tuple and ADT layouts in their joint by-value dependency order.
-- Forward-declared recursive ADT pointers impose no ordering constraint.
structuralTypeDecls :: CgConfig -> [Kind] -> [Kind] -> Doc
structuralTypeDecls cfg adts tuples = vcat (map declaration orderedKinds)
 where allKinds        = tuples ++ adts
       availableKinds  = Set.fromList allKinds
       dependencyNodes = [(kind, kind, filter (`Set.member` availableKinds) (dependencies kind)) | kind <- allKinds]
       orderedKinds     = concatMap orderedComponent (DG.stronglyConnComp dependencyNodes)

       dependencies (KTuple fieldKinds) = [ resolved
                                           | fieldKind <- fieldKinds
                                           , let resolved = resolveADTReferences adts fieldKind
                                           , isTuple resolved || isConcreteADTKind resolved
                                           ]
       dependencies kind
         | isConcreteADTKind kind = adtDeclarationDependencies adts kind
         | True                   = []

       orderedComponent (DG.AcyclicSCC kind) = [kind]
       orderedComponent (DG.CyclicSCC kinds) = error $ "SBV->C: Recursive by-value tuple/ADT layout: " ++ show kinds

       declaration kind
         | isTuple kind           = tupleTypeDecls [kind]
         | isConcreteADTKind kind = adtTypeDeclsFor cfg adts [kind]
         | True                   = error $ "SBV->C: Expected a tuple or ADT layout, received " ++ show kind

-- | Pretty print a function type. A single return value uses C's return
-- position when its representation permits; aggregate return groups and
-- multiple returns are passed as output parameters by the caller.
pprCFunHeader :: CgConfig -> String -> [(String, CgVal)] -> [(String, CgVal)] -> Maybe SV -> Doc
pprCFunHeader cfg fn ins outs mbRet = retType <+> text fn P.<> parens (fsep (punctuate comma params))
  where params  = map (mkParam cfg) ins ++ map (mkPParam cfg) outs ++ exactResult
        retType = case mbRet of
                    Just sv | isArray sv                           -> text (arrayOutputCType (kindOf sv))
                    Just sv | not (isExactGMPKind cfg (kindOf sv)) -> pprCWord False sv
                    _                                              -> text "void"

        exactResult = case mbRet of
                        Just sv | isExactGMPKind cfg (kindOf sv) -> [text (gmpOutputType (kindOf sv)) <+> text "__result"]
                        _                                        -> []

-- | Render a generated C input parameter.
mkParam :: CgConfig -> (String, CgVal) -> Doc
mkParam _   (n, CgAtomic sv)
  | isArray sv = text "const" <+> text (arrayInputCType (kindOf sv)) <+> text n
mkParam _   (n, CgAtomic sv)     = pprCWord True sv <+> text n
mkParam _   (_, CgArray [])        = die "mkParam: CgArray with no elements!"
mkParam cfg (n, CgArray (sv:_))
  | isExactGMPKind cfg kind = text "const" <+> text (gmpArrayType kind) <+> text "*" P.<> text n
  | True                    = pprCWord True sv <+> text "*" P.<> text n
  where kind = kindOf sv

-- | Render a generated C output parameter.
mkPParam :: CgConfig -> (String, CgVal) -> Doc
mkPParam _   (n, CgAtomic sv)
  | isArray sv = text (arrayOutputCType (kindOf sv)) <+> text "*" P.<> text n
mkPParam cfg (n, CgAtomic sv)
  | isExactGMPKind cfg (kindOf sv) = text (gmpOutputType (kindOf sv)) <+> text n
  | True                           = pprCWord False sv <+> text "*" P.<> text n
mkPParam _   (_, CgArray [])        = die "mkPParam: CgArray with no elements!"
mkPParam cfg (n, CgArray (sv:_))
  | isExactGMPKind cfg kind = text (gmpArrayType kind) <+> text "*" P.<> text n
  | isArray kind            = text (arrayOutputCType kind) <+> text "*" P.<> text n
  | True                    = pprCWord False sv <+> text "*" P.<> text n
  where kind = kindOf sv

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
                KBounded False w -> "SWord" ++ show w
                KBounded True  w -> "SInt"  ++ show w
                k@KArray{}        -> arrayCType k
                k@KTuple{}        -> tupleCType k
                k@KADT{}
                  | not (isRoundingMode k) && not (isUninterpreted k) -> adtCType k
                k@KFP{}           -> arbitraryFPCType k
                KString           -> "SString"
                KChar             -> "SChar"
                k@KList{}         -> listCType k
                k@KSet{}          -> setCType k
                k                -> show k

-- | The printf specifier for the type
specifier :: CgConfig -> SV -> Doc
specifier cfg = specifierKind cfg . kindOf

-- | Return the @printf@ conversion for a supported scalar kind.
specifierKind :: CgConfig -> Kind -> Doc
specifierKind cfg kind = case kind of
  KVar{}        -> die $ "variable sort: " ++ show kind
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
  KList k       -> die $ "list sort: "   ++ show k
  KSet  k       -> die $ "set sort: "    ++ show k
  KApp s _      -> die $ "ADT app: "     ++ s
  k@(KADT s _ _)
    | isRoundingMode k -> text "%d"
    | True             -> die $ "ADT: " ++ s
  KTuple k      -> die $ "tuple sort: "  ++ show k
  KArray  k1 k2 -> die $ "array sort: "  ++ show (k1, k2)
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
mkConst _   cv
  | Just d <- roundingModeConst cv = d
mkConst cfg cv
  | Just d <- arrayConst (mkConst cfg) cv = d
mkConst cfg cv
  | Just d <- tupleConst (mkConst cfg) cv = d
mkConst cfg cv
  | Just d <- adtConst (mkConst cfg) cv = d
mkConst cfg cv
  | Just d <- listConst (mkConst cfg) cv = d
mkConst cfg cv
  | Just d <- setConst (mkConst cfg) cv = d
mkConst cfg cv
  | Just d <- gmpConst cfg cv = d
mkConst _   (CV k (CInteger i))
  | Just d <- wideBVConst k i = d
mkConst cfg (CV KReal (CAlgReal (AlgRational _ r))) = double (fromRational r :: Double) P.<> sRealSuffix (fromJust (cgReal cfg))
  where sRealSuffix CgFloat      = text "F"
        sRealSuffix CgDouble     = empty
        sRealSuffix CgLongDouble = text "L"
mkConst cfg (CV KUnbounded       (CInteger i)) = showSizedConst (cgShowU8InHex cfg) i (True, fromJust (cgInteger cfg))
mkConst cfg (CV (KBounded sg sz) (CInteger i)) = showSizedConst (cgShowU8InHex cfg) i (sg,   sz)
mkConst cfg (CV KBool            (CInteger i)) = showSizedConst (cgShowU8InHex cfg) i (False, 1)
mkConst _   (CV KFloat           (CFloat f))   = text $ showCFloat f
mkConst _   (CV KDouble          (CDouble d))  = text $ showCDouble d
mkConst _   (CV k@KFP{}          (CFP fp))     = fromJust (arbitraryFPConst k fp)
mkConst _   cv@(CV KString       CString{})     = fromJust (textConst cv)
mkConst _   cv@(CV KChar         CChar{})       = fromJust (textConst cv)
mkConst _   cv                                 = die $ "mkConst: " ++ show cv

showSizedConst :: Bool -> Integer -> (Bool, Int) -> Doc
showSizedConst _   i   (False,  1) = text (if i == 0 then "false" else "true")
showSizedConst u8h i t@(False,  8)
  | u8h                            = text $ T.unpack (chex False True t i)
  | True                           = integer i
showSizedConst _   i   (True,   8) = integer i
showSizedConst _   i t@(False, 16) = text $ T.unpack $ chex False True t i
showSizedConst _   i t@(True,  16) = text $ T.unpack $ chex False True t i
showSizedConst _   i t@(False, 32) = text $ T.unpack $ chex False True t i
showSizedConst _   i t@(True,  32) = text $ T.unpack $ chex False True t i
showSizedConst _   i t@(False, 64) = text $ T.unpack $ chex False True t i
showSizedConst _   i t@(True,  64) = text $ T.unpack $ chex False True t i
showSizedConst _   i   (s, sz)     = die $ "Constant " ++ show i ++ " at type " ++ (if s then "SInt" else "SWord") ++ show sz

-- | Generate a makefile. The first argument is True if we have a driver.
genMake :: Bool -> String -> String -> [String] -> Doc
genMake ifdr fn dn ldFlags = foldr1 ($$) [l | (True, l) <- lns]
 where ifld = not (null ldFlags)
       gmp  = "-lgmp" `elem` ldFlags
       ld | ifld = text "${LDFLAGS}"
          | True = empty
       renderedLDFlags = unwords $ filter (/= "-lgmp") ldFlags ++ ["${GMP_LIBS}" | gmp]
       gmpCFlags
         | gmp       = text " ${GMP_CFLAGS}"
         | True      = empty
       lns = [ (True, text "# Makefile for" <+> nm P.<> text ". Automatically generated by SBV. Do not edit!")
             , (True, text "")
             , (True, text "# include any user-defined .mk file in the current directory.")
             , (True, text "-include *.mk")
             , (True, text "")
             , (True, text "CC?=gcc")
             , (True, text "CCFLAGS?=-Wall -O3 -DNDEBUG -fomit-frame-pointer")
             , (gmp,  text "GMP_CFLAGS?=$(shell pkg-config --cflags gmp)")
             , (gmp,  text "GMP_LIBS?=$(shell pkg-config --libs gmp)")
             , (ifld, text "LDFLAGS?=" P.<> text renderedLDFlags)
             , (True, text "")
             , (ifdr, text "all:" <+> nmd)
             , (ifdr, text "")
             , (True, nmo P.<> text (": " ++ ppSameLine (hsep [nmc, nmh])))
             , (True, text "\t${CC} ${CCFLAGS}" P.<> gmpCFlags <+> text "-c $< -o $@")
             , (True, text "")
             , (ifdr, nmdo P.<> text ":" <+> nmdc)
             , (ifdr, text "\t${CC} ${CCFLAGS}" P.<> gmpCFlags <+> text "-c $< -o $@")
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
genHeader :: (Maybe Int, Maybe CgSRealType) -> String -> [Doc] -> Doc -> Doc -> Doc
genHeader (ik, rk) fn sigs protos extraTypes =
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
  $$ extraTypes
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

-- | Test whether an ADT value needs the caller-owned deep-storage ABI.
isOwnedADT :: CgConfig -> [Kind] -> SV -> Bool
isOwnedADT cfg adts sv = isADT sv
                     && not (isRoundingMode sv)
                     && adtNeedsOwnership cfg adts (kindOf sv)

-- | Generate an example driver program
genDriver :: CgConfig -> [Kind] -> [Integer] -> String -> [(String, CgVal)] -> [(String, CgVal)] -> Maybe SV -> [Doc]
genDriver cfg adts randVals fn inps outs mbRet
  | null inputArrayKinds = [pre, include, printHelpers, plainHeader, body, post]
  | True                 = [pre, include, callbacks, printHelpers, header, body, post]
 where pre         =  text "/* Example driver program for" <+> nm P.<> text ". */"
                   $$ text "/* Automatically generated by SBV. Edit as you see fit! */"
                   $$ text ""
                   $$ text "#include <stdio.h>"
       include     = text "#include" <+> doubleQuotes (nm P.<> text ".h")
       callbacks   = vcat (map (arrayDriverCallback cfg) inputArrayKinds)
       plainHeader = text ""
                   $$ text "int main(void)"
                   $$ text "{"
       header      =  text ""
                   $$ text "int main(void)"
                   $$ text "{"
       body        =  text ""
                   $$ nest 2 (   vcat (map mkInp pairedInputs)
                           $$ vcat (map mkOut outs)
                           $$ sepIf (not (null [() | (_, _, CgArray{}) <- pairedInputs]) || not (null outs))
                           $$ call
                           $$ text ""
                           $$ (case mbRet of
                              Just sv | isArray sv
                                      -> displayArray "__result" fcall resultVar (kindOf sv)
                              Just sv | isTuple sv
                                      -> displayTuple fcall resultVar (kindOf sv)
                              Just sv | isADT sv && not (isRoundingMode sv)
                                      -> displayADT fcall resultVar (kindOf sv)
                              Just sv | isList sv
                                      -> displayList fcall resultVar (kindOf sv)
                              Just sv | isSet sv
                                      -> displaySet fcall resultVar (kindOf sv)
                              Just sv | isWideBV (kindOf sv)
                                      -> text "printf" P.<> parens (printQuotes (fcall <+> text "=")) P.<> semi
                                      $$ wideBVPrint (kindOf sv) resultVar P.<> semi
                                      $$ text "printf(\"\\n\");"
                              Just sv | isFP (kindOf sv)
                                      -> text "printf" P.<> parens (printQuotes (fcall <+> text "=")) P.<> semi
                                      $$ arbitraryFPPrint (kindOf sv) resultVar P.<> semi
                                      $$ text "printf(\"\\n\");"
                              Just sv | isExactGMPKind cfg (kindOf sv)
                                      -> text "printf" P.<> parens (printQuotes (fcall <+> text "=")) P.<> semi
                                      $$ gmpPrint (kindOf sv) resultVar P.<> semi
                                      $$ text "printf(\"\\n\");"
                              Just sv | kindOf sv `elem` [KChar, KString]
                                      -> text "printf" P.<> parens (printQuotes (fcall <+> text "=")) P.<> semi
                                      $$ textPrint (kindOf sv) resultVar P.<> semi
                                      $$ text "printf(\"\\n\");"
                              Just sv -> text "printf" P.<> parens (printQuotes (fcall <+> text "=" <+> specifier cfg sv P.<> text "\\n")
                                                                              P.<> comma <+> resultVar) P.<> semi
                              Nothing -> text "printf" P.<> parens (printQuotes (fcall <+> text "->\\n")) P.<> semi)
                           $$ vcat (map display outs)
                           $$ driverCleanup
                           )
       post        =   text ""
                   $+$ nest 2 (text "return 0" P.<> semi)
                   $$  text "}"
                   $$  text ""
       nm                 = text fn
       inputArrayKinds    = nub . concatMap collectInputArrays $ concatMap inputKinds inps
       inputKinds (_, CgAtomic sv) = [kindOf sv]
       inputKinds (_, CgArray svs) = map kindOf svs

       collectInputArrays = collect Set.empty
        where collect visited kind
                | kind `Set.member` visited = []
                | KApp{} <- kind
                = collect nextVisited (resolveADTReferences adts kind)
                | KArray keyKind valueKind <- kind
                = kind : collect nextVisited keyKind ++ collect nextVisited valueKind
                | KTuple fieldKinds <- kind
                = concatMap (collect nextVisited) fieldKinds
                | KList elementKind <- kind
                = collect nextVisited elementKind
                | KSet elementKind <- kind
                = collect nextVisited elementKind
                | isConcreteADTKind kind
                = concatMap (concatMap (collect nextVisited) . snd) (adtConstructors adts kind)
                | True
                = []
               where nextVisited = Set.insert kind visited
       pairedInputs = matchRands randVals inps
       inputSeeds   = matchInputSeeds randVals inps
       matchRands _      []                                 = []
       matchRands []     _                                  = die "Run out of driver values!"
       matchRands (r:rs) ((n, CgAtomic sv)            : cs)
         | KArray _ valueKind <- kindOf sv                   = ([mkRValKind valueKind r], n, CgAtomic sv) : matchRands rs cs
       matchRands (r:rs) ((n, CgAtomic sv)            : cs) = ([mkRVal sv r], n, CgAtomic sv) : matchRands rs cs
       matchRands _      ((n, CgArray [])             : _ ) = die $ "Unsupported empty array input " ++ show n
       matchRands rs     ((n, a@(CgArray sws@(sv:_))) : cs)
          | length frs /= l                                 = die "Run out of driver values!"
          | True                                            = (map (mkRVal sv) frs, n, a) : matchRands srs cs
          where l          = length sws
                (frs, srs) = splitAt l rs
       matchInputSeeds _      []                            = []
       matchInputSeeds []     _                             = die "Run out of driver values!"
       matchInputSeeds (r:rs) ((n, CgAtomic{})        : cs) = (n, r) : matchInputSeeds rs cs
       matchInputSeeds _      ((n, CgArray [])        : _ ) = die $ "Unsupported empty array input " ++ show n
       matchInputSeeds rs     ((n, CgArray values@(_:_)) : cs)
         | seed : _ <- seeds
         , length seeds == length values                       = (n, seed) : matchInputSeeds rest cs
         | True                                                = die "Run out of driver values!"
        where (seeds, rest) = splitAt (length values) rs
       inputSeed n = case lookup n inputSeeds of
                       Just seed -> seed
                       Nothing   -> die $ "Missing driver seed for composite input " ++ show n
       mkRVal sv = mkRValKind (kindOf sv)
       mkRValKind kind r
         | isRoundingMode kind            = roundingModeDriverValue r
         | isExactGMPKind cfg kind         = integer r
         | kind `elem` [KChar, KString]    = textDriverValue kind r
         | isList kind                     = listDriverValue mkRValKind kind r
         | isSet kind                      = setDriverValue mkRValKind kind r
         | KTuple fieldKinds <- kind       = tupleValue kind (zipWith mkField fieldKinds [0 :: Integer ..])
         | isADT kind                      = adtDriverValue adts mkRValKind kind r
         | True                            = mkConst cfg $ mkConstCV kind r
         where mkField fieldKind offset = mkRValKind fieldKind (r + offset)
       driverValueInit kind externalName seed
         | KApp{} <- kind                   = driverValueInit (resolveADTReferences adts kind) externalName seed
         | isExactGMPKind cfg kind         = gmpDriverInit kind (text externalName) (integer seed)
         | isArray kind                    = initializeArray kind externalName seed
         | collectionUsesADT kind          = adtCollectionDriverInit cfg adts mkRValKind driverValueInit kind externalName seed
         | listNeedsDriverInit cfg kind    = listDriverInit cfg mkRValKind driverValueInit kind externalName seed
         | setNeedsDriverInit cfg kind     = setDriverInit cfg mkRValKind driverValueInit kind externalName seed
         | tupleNeedsOwnership cfg kind    = tupleDriverInit cfg mkRValKind driverValueInit kind externalName seed
         | isConcreteADTKind kind
         , adtNeedsOwnership cfg adts kind = adtDriverInit cfg adts mkRValKind driverValueInit kind externalName seed
         | isConcreteADTKind kind          = text (adtCType kind) <+> text externalName <+> text "="
                                           <+> adtDriverValue adts mkRValKind kind seed P.<> semi
         | True                            = text "const" <+> text (showCType kind) <+> text externalName <+> text "="
                                           <+> mkRValKind kind seed P.<> semi
       initializeArray kind@(KArray _ valueKind) externalName seed
         = let defaultName = externalName ++ "_default"
               inputName   = externalName ++ "_input"
           in driverValueInit valueKind defaultName seed
              $$ arrayDriverInput cfg kind inputName defaultName
              $$ arrayDriverStoredInput kind externalName inputName
              $$ driverValueClear valueKind defaultName
       initializeArray kind _ _ = die $ "Expected an array driver kind, received " ++ show kind
       driverValueClear kind externalName
         | isExactGMPKind cfg kind         = gmpDriverClear kind (text externalName)
         | isArray kind                    = text (CTypes.arrayStoredReleaseName kind) P.<> parens (text "&" P.<> text externalName) P.<> semi
         | isList kind                     = listDriverClear cfg kind externalName
         | isSet kind                      = setDriverClear cfg kind externalName
         | tupleNeedsOwnership cfg kind    = text (tupleOwnedReleaseName kind) P.<> parens (text "&" P.<> text externalName) P.<> semi
         | isConcreteADTKind kind
         , adtNeedsOwnership cfg adts kind = text (adtOwnedReleaseName kind) P.<> parens (text "&" P.<> text externalName) P.<> semi
         | True                            = empty
       mkInp (_, n, CgAtomic sv)
         | KArray _ valueKind <- kindOf sv
         = let defaultName = n ++ "_default"
           in driverValueInit valueKind defaultName (inputSeed n)
              $$ arrayDriverInput cfg (kindOf sv) n defaultName
       mkInp ([v], n, CgAtomic sv)
         | isExactGMPKind cfg (kindOf sv)      = gmpDriverInit (kindOf sv) (text n) v
         | collectionUsesADT (kindOf sv)       = adtCollectionDriverInit cfg adts mkRValKind driverValueInit (kindOf sv) n (inputSeed n)
         | listNeedsDriverInit cfg (kindOf sv) = listDriverInit cfg mkRValKind driverValueInit (kindOf sv) n (inputSeed n)
         | setNeedsDriverInit cfg (kindOf sv)  = setDriverInit cfg mkRValKind driverValueInit (kindOf sv) n (inputSeed n)
         | tupleNeedsOwnership cfg (kindOf sv) = tupleDriverInit cfg mkRValKind driverValueInit (kindOf sv) n (inputSeed n)
         | isOwnedADT cfg adts sv              = adtDriverInit cfg adts mkRValKind driverValueInit (kindOf sv) n (inputSeed n)
       mkInp (_,   _, CgAtomic{})         = empty  -- constant, no need to declare
       mkInp (_,   n, CgArray [])         = die $ "Unsupported empty array value for " ++ show n
       mkInp (vs, n, CgArray sws@(sv:_))
         | isExactGMPKind cfg kind = text (gmpArrayType kind) <+> text n P.<> brackets (int lengthOfArray) P.<> semi
                                  $$ vcat (zipWith initialize [0 :: Int ..] vs)
                                  $$ displayInputArray
         | True                    = pprCWord True sv <+> text n P.<> brackets (int lengthOfArray) <+> text "= {"
                                  $$ nest 4 (fsep (punctuate comma (align vs)))
                                  $$ text "};"
                                  $$ displayInputArray
         where kind          = kindOf sv
               lengthOfArray = length sws

               initialize index = gmpDriverInitialize kind (text n P.<> brackets (int index))

               displayInputArray = text ""
                                $$ text "printf" P.<> parens (printQuotes (text "Contents of input array" <+> text n P.<> text ":\\n")) P.<> semi
                                $$ display (n, CgArray sws)
                                $$ text ""
       mkOut (v, CgAtomic sv)
         | isArray sv                          = text (arrayOutputCType (kindOf sv)) <+> text v <+> text "=" <+> braces (text "0") P.<> semi
         | isExactGMPKind cfg (kindOf sv)      = gmpDriverInit (kindOf sv) (text v) (text "0")
         | kindOf sv == KString                = text "SString" <+> text v <+> text "=" <+> braces (text "0") P.<> semi
         | isList sv                           = text (listCType (kindOf sv)) <+> text v <+> text "=" <+> braces (text "0") P.<> semi
         | isSet sv                            = text (setCType (kindOf sv)) <+> text v <+> text "=" <+> braces (text "0") P.<> semi
         | tupleNeedsOwnership cfg (kindOf sv) = text (tupleCType (kindOf sv)) <+> text v
                                             <+> text "=" <+> braces (text "0") P.<> semi
         | isOwnedADT cfg adts sv              = text (adtCType (kindOf sv)) <+> text v
                                             <+> text "=" <+> braces (text "0") P.<> semi
         | True                                = pprCWord False sv <+> text v P.<> semi
       mkOut (v, CgArray [])         = die $ "Unsupported empty array value for " ++ show v
       mkOut (v, CgArray sws@(sv:_))
         | isExactGMPKind cfg kind = text (gmpArrayType kind) <+> text v P.<> brackets (int lengthOfArray) P.<> semi
                                  $$ vcat [gmpDriverInitialize kind (text v P.<> brackets (int index)) (text "0") | index <- [0 .. lengthOfArray - 1]]
         | isArray kind            = text (arrayOutputCType kind) <+> text v P.<> brackets (int lengthOfArray)
                                  <+> text "=" <+> braces (text "0") P.<> semi
         | True                    = pprCWord False sv <+> text v P.<> brackets (int lengthOfArray) P.<> semi
         where kind          = kindOf sv
               lengthOfArray = length sws
       resultVar = text "__result"
       call = case mbRet of
                Nothing -> fcall P.<> semi
                Just sv
                  | isExactGMPKind cfg (kindOf sv)      -> gmpDriverInit (kindOf sv) resultVar (text "0")
                                                        $$ fcall P.<> semi
                  | isArray sv                          -> text (arrayOutputCType (kindOf sv)) <+> resultVar
                                                       <+> text "=" <+> fcall P.<> semi
                  | tupleNeedsOwnership cfg (kindOf sv) -> text (tupleCType (kindOf sv)) <+> resultVar
                                                       <+> text "=" <+> fcall P.<> semi
                  | isOwnedADT cfg adts sv              -> text (adtCType (kindOf sv)) <+> resultVar
                                                       <+> text "=" <+> fcall P.<> semi
                  | kindOf sv == KString                -> text "const SString" <+> resultVar <+> text "=" <+> fcall P.<> semi
                  | isList sv                           -> text "const" <+> text (listCType (kindOf sv)) <+> resultVar
                                                       <+> text "=" <+> fcall P.<> semi
                  | isSet sv                            -> text "const" <+> text (setCType (kindOf sv)) <+> resultVar
                                                       <+> text "=" <+> fcall P.<> semi
                  | True                                -> pprCWord True sv <+> resultVar <+> text "=" <+> fcall P.<> semi
       fcall = nm P.<> parens (fsep (punctuate comma (map mkCVal pairedInputs ++ map mkOVal outs ++ exactResultArg)))
       exactResultArg = case mbRet of
                          Just sv | isExactGMPKind cfg (kindOf sv) -> [resultVar]
                          _                                        -> []
       mkCVal ([v], n, CgAtomic sv)
         | isArray sv                          = text n
         | isExactGMPKind cfg (kindOf sv)      = text n
         | listNeedsDriverInit cfg (kindOf sv) = text n
         | setNeedsDriverInit cfg (kindOf sv)  = text n
         | tupleNeedsOwnership cfg (kindOf sv) = text n
         | isOwnedADT cfg adts sv              = text n
         | True                                = v
       mkCVal (vs,  n, CgAtomic{}) = die $ "Unexpected driver value computed for " ++ show n ++ render (hcat vs)
       mkCVal (_,   n, CgArray{})  = text n
       mkOVal (n, CgAtomic sv)
         | isExactGMPKind cfg (kindOf sv) = text n
         | True                           = text "&" P.<> text n
       mkOVal (n, CgArray{})       = text n
       display (n, CgAtomic sv)
         | isArray sv                           = displayArray n (text n) (text n) (kindOf sv)
         | isTuple sv                           = displayTuple (text n) (text n) (kindOf sv)
         | isADT sv && not (isRoundingMode sv) = displayADT (text n) (text n) (kindOf sv)
         | isList sv                            = displayList (text n) (text n) (kindOf sv)
         | isSet sv                             = displaySet (text n) (text n) (kindOf sv)
         | isWideBV (kindOf sv)                 = text "printf" P.<> parens (printQuotes (text " " <+> text n <+> text "=")) P.<> semi
                                                $$ wideBVPrint (kindOf sv) (text n) P.<> semi
                                                $$ text "printf(\"\\n\");"
         | isFP (kindOf sv)                     = text "printf" P.<> parens (printQuotes (text " " <+> text n <+> text "=")) P.<> semi
                                                $$ arbitraryFPPrint (kindOf sv) (text n) P.<> semi
                                                $$ text "printf(\"\\n\");"
         | isExactGMPKind cfg (kindOf sv)       = text "printf" P.<> parens (printQuotes (text " " <+> text n <+> text "=")) P.<> semi
                                                $$ gmpPrint (kindOf sv) (text n) P.<> semi
                                                $$ text "printf(\"\\n\");"
         | kindOf sv `elem` [KChar, KString]     = text "printf" P.<> parens (printQuotes (text " " <+> text n <+> text "=")) P.<> semi
                                                $$ textPrint (kindOf sv) (text n) P.<> semi
                                                $$ text "printf(\"\\n\");"
         | True                                 = text "printf" P.<> parens (printQuotes (text " " <+> text n <+> text "=" <+> specifier cfg sv
                                                                                         P.<> text "\\n") P.<> comma <+> text n) P.<> semi
       display (n, CgArray [])         = die $ "Unsupported empty array value for " ++ show n
       display (n, CgArray sws@(sv:_)) = text "int" <+> nctr P.<> semi
                                      $$ text "for(" P.<> nctr <+> text "= 0;" <+> nctr <+> text "<" <+> int len <+> text "; ++" P.<> nctr P.<> text ")"
                                      $$ text "{"
                                      $$ nest 2 displayEntry
                                      $$ text "}"
         where nctr      = text n P.<> text "_ctr"
               entry     = text n P.<> text "[" P.<> nctr P.<> text "]"
               entrySpec = text n P.<> text "[%" P.<> int tab P.<> text "d]"
               kind      = kindOf sv
               len       = length sws
               tab       = length $ show (len - 1)

               displayEntry
                 | isArray kind = displayArrayEntry kind
                 | True         = text "printf" P.<> parens (printQuotes (text " " <+> entrySpec <+> text "= ") P.<> comma <+> nctr) P.<> semi
                               $$ printValue kind entry
                               $$ text "printf(\"\\n\");"

               displayArrayEntry arrayKind@(KArray keyKind valueKind)
                 =  keySetup
                 $$ text "printf" P.<> parens (printQuotes (text " " <+> (entrySpec P.<> text "[0] =")) P.<> comma <+> nctr) P.<> semi
                 $$ printValue valueKind arrayValue
                 $$ text "printf(\"\\n\");"
                 $$ keyCleanup
                where keyName    = "__sbv_array_key_" ++ n
                      key        = text keyName
                      keySetup   = driverValueInit keyKind keyName 0
                      keyCleanup = driverValueClear keyKind keyName
                      arrayValue  = text (arrayOutputReadName arrayKind)
                                 P.<> parens (fsep (punctuate comma [entry, key]))
               displayArrayEntry arrayKind = die $ "Expected an array return-group element, received " ++ show arrayKind

       displayArray stem label descriptor kind@(KArray keyKind valueKind)
         =  keySetup
         $$ text "printf" P.<> parens (printQuotes (text " " <+> label P.<> text "[0] =")) P.<> semi
         $$ printArrayValue
         $$ text "printf(\"\\n\");"
         $$ keyCleanup
        where keyName = "__sbv_array_key_" ++ stem
              key     = text keyName

              keySetup   = driverValueInit  keyKind keyName 0
              keyCleanup = driverValueClear keyKind keyName

              value = text (arrayOutputReadName kind) P.<> parens (fsep (punctuate comma [descriptor, key]))
              printArrayValue = printValue valueKind value
       displayArray _ _ _ kind = die $ "Expected an array output, received " ++ show kind

       displayTuple label value kind@KTuple{}
         =  text "printf" P.<> parens (printQuotes (text " " <+> label <+> text "=")) P.<> semi
         $$ printTupleValue value kind
         $$ text "printf(\"\\n\");"
       displayTuple _ _ kind = die $ "Expected a tuple output, received " ++ show kind

       displayADT label value kind
         =  text "printf" P.<> parens (printQuotes (text " " <+> label <+> text "=")) P.<> semi
         $$ adtPrint adts printValue kind value
         $$ text "printf(\"\\n\");"

       displayList label value kind@KList{}
         =  text "printf" P.<> parens (printQuotes (text " " <+> label <+> text "=")) P.<> semi
         $$ listPrint printValue kind value
         $$ text "printf(\"\\n\");"
       displayList _ _ kind = die $ "Expected a list output, received " ++ show kind

       displaySet label value kind@KSet{}
         =  text "printf" P.<> parens (printQuotes (text " " <+> label <+> text "=")) P.<> semi
         $$ setPrint printValue kind value
         $$ text "printf(\"\\n\");"
       displaySet _ _ kind = die $ "Expected a set output, received " ++ show kind

       printHelpers = adtPrintHelpers adts printValue

       printTupleValue _     (KTuple []) = text "printf(\"()\");"
       printTupleValue value (KTuple fieldKinds)
         =  text "printf(\"(\");"
         $$ vcat (intersperse (text "printf(\", \");") (zipWith printField [1 :: Int ..] fieldKinds))
         $$ text "printf(\")\");"
        where printField index fieldKind = printValue fieldKind (parens value P.<> text "." P.<> text (tupleFieldName index))
       printTupleValue _ kind = die $ "Expected a tuple value, received " ++ show kind

       printValue kind value
         | KTuple{} <- kind                        = printTupleValue value kind
         | KList{} <- kind                         = listPrint printValue kind value
         | KSet{} <- kind                          = setPrint printValue kind value
         | KArray{} <- kind                        = printStoredArray value kind
         | isADT kind && not (isRoundingMode kind) = adtPrint adts printValue kind value
         | isWideBV kind                           = wideBVPrint kind value P.<> semi
         | isFP kind                               = arbitraryFPPrint kind value P.<> semi
         | isExactGMPKind cfg kind                 = gmpPrint kind value P.<> semi
         | kind `elem` [KChar, KString]             = textPrint kind value P.<> semi
         | True                                    = text "printf" P.<> parens (printQuotes (specifierKind cfg kind) P.<> comma <+> value) P.<> semi

       printStoredArray descriptor kind@(KArray keyKind valueKind)
         =  text "{"
         $$ nest 2 (   text "if" P.<> parens (descriptor <+> text "== NULL") <+> text "abort" P.<> parens empty P.<> semi
                    $$ keySetup
                    $$ text "printf(\"[0] =\");"
                    $$ printValue valueKind storedValue
                    $$ keyCleanup
                   )
         $$ text "}"
        where keyName     = "__sbv_array_stored_key_" ++ kindTag kind
              key         = text keyName
              keySetup    = driverValueInit keyKind keyName 0
              keyCleanup  = driverValueClear keyKind keyName
              storedValue = text (arrayOutputReadName kind)
                         P.<> parens (fsep (punctuate comma [text "*" P.<> parens descriptor, key]))
       printStoredArray _ kind = die $ "Expected a stored array, received " ++ show kind

       driverCleanup = vcat $ inputCleanup ++ outputCleanup ++ returnCleanup
         where inputCleanup  = [ gmpDriverClear (kindOf sv) (text n)
                               | (_, n, CgAtomic sv) <- pairedInputs
                               , isExactGMPKind cfg (kindOf sv)
                               ]
                              ++ [listDriverClear cfg (kindOf sv) n
                                 | (_, n, CgAtomic sv) <- pairedInputs
                                 , listNeedsDriverInit cfg (kindOf sv)
                                 ]
                              ++ [setDriverClear cfg (kindOf sv) n
                                 | (_, n, CgAtomic sv) <- pairedInputs
                                 , setNeedsDriverInit cfg (kindOf sv)
                                 ]
                              ++ [releaseTuple sv n
                                 | (_, n, CgAtomic sv) <- pairedInputs
                                 , tupleNeedsOwnership cfg (kindOf sv)
                                 ]
                              ++ [driverValueClear valueKind (n ++ "_default")
                                 | (_, n, CgAtomic sv) <- pairedInputs
                                 , KArray _ valueKind <- [kindOf sv]
                                 ]
                              ++ [releaseADT sv n
                                 | (_, n, CgAtomic sv) <- pairedInputs
                                 , isOwnedADT cfg adts sv
                                 ]
                              ++ [gmpDriverClear (kindOf sv) (text n P.<> brackets (int index))
                                 | (_, n, CgArray svs) <- pairedInputs
                                 , (index, sv) <- zip [0 :: Int ..] svs
                                 , isExactGMPKind cfg (kindOf sv)
                                 ]
               outputCleanup = [ gmpDriverClear (kindOf sv) (text n)
                               | (n, CgAtomic sv) <- outs
                               , isExactGMPKind cfg (kindOf sv)
                               ]
                            ++ [releaseTuple sv n
                               | (n, CgAtomic sv) <- outs
                               , tupleNeedsOwnership cfg (kindOf sv)
                               ]
                            ++ [text (arrayOutputReleaseName (kindOf sv)) P.<> parens (text "&" P.<> text n) P.<> semi
                               | (n, CgAtomic sv) <- outs
                               , isArray sv
                               ]
                            ++ [releaseADT sv n
                               | (n, CgAtomic sv) <- outs
                               , isOwnedADT cfg adts sv
                               ]
                            ++ [textRelease (text n)
                               | (n, CgAtomic sv) <- outs
                               , kindOf sv == KString
                               ]
                            ++ [listRelease (kindOf sv) (text n)
                               | (n, CgAtomic sv) <- outs
                               , isList sv
                               ]
                            ++ [setRelease (kindOf sv) (text n)
                               | (n, CgAtomic sv) <- outs
                               , isSet sv
                               ]
                            ++ [outputArrayValueClear (kindOf sv) (n ++ "[" ++ show index ++ "]")
                               | (n, CgArray svs) <- outs
                               , (index, sv) <- zip [0 :: Int ..] svs
                               ]
               returnCleanup = case mbRet of
                                 Just sv | isExactGMPKind cfg (kindOf sv)      -> [gmpDriverClear (kindOf sv) resultVar]
                                 Just sv | isArray sv                          -> [text (arrayOutputReleaseName (kindOf sv)) P.<> parens (text "&" P.<> resultVar) P.<> semi]
                                 Just sv | tupleNeedsOwnership cfg (kindOf sv) -> [releaseTuple sv "__result"]
                                 Just sv | isOwnedADT cfg adts sv              -> [releaseADT sv "__result"]
                                 Just sv | kindOf sv == KString                -> [textRelease resultVar]
                                 Just sv | isList sv                           -> [listRelease (kindOf sv) resultVar]
                                 Just sv | isSet sv                            -> [setRelease (kindOf sv) resultVar]
                                 _                                             -> []

               releaseTuple sv = releaseOwned (tupleOwnedReleaseName (kindOf sv))
               releaseADT   sv = releaseOwned (adtOwnedReleaseName   (kindOf sv))

               releaseOwned helper externalName = text helper
                                                 P.<> parens (text "&" P.<> text externalName)
                                                 P.<> semi

               outputArrayValueClear kind externalName
                 | isArray kind    = text (arrayOutputReleaseName kind)
                                  P.<> parens (text "&" P.<> text externalName)
                                  P.<> semi
                 | kind == KString = textRelease (text externalName)
                 | isList kind     = listRelease kind (text externalName)
                 | isSet kind      = setRelease kind (text externalName)
                 | True            = driverValueClear kind externalName

-- | Generate the C program
genCProg :: CgConfig
         -> [Kind]
         -> [Kind]
         -> [Kind]
         -> String
         -> Doc
         -> Result
         -> [(String, CgVal)]
         -> [(String, CgVal)]
         -> Maybe SV
         -> Doc
         -> ([Doc], Set.Set CRequirement)
genCProg cfg adts lists sets fn proto
         (Result pinfo kindInfo _tvals _ovals cgs topInps (_, preConsts) tbls _uis definitions
                 (SBVPgm asgns) cstrs origAsserts _)
         inVars outVars mbRet extDecls
  | not (null unsupportedSets)
  = notyet $ "Sets with element kinds " ++ intercalate ", " (map (show . setElementKind) unsupportedSets)
  | any assignmentUsesSet arrayLambdaAssignments
  = notyet "Sets in array lambdas"
  | any containsNestedSet kindInfo
  = notyet "Sets nested in arrays or unsupported aggregate types"
  | not (null unsupportedLists)
  = notyet $ "Lists with element kinds " ++ intercalate ", " (map (show . listElementKind) unsupportedLists)
  | any assignmentUsesList arrayLambdaAssignments
  = notyet "Lists in array lambdas"
  | any containsNestedList kindInfo
  = notyet "Lists nested in arrays or unsupported aggregate types"
  | any assignmentUsesText arrayLambdaAssignments
  = notyet "Characters or strings in array lambdas"
  | not (null usorts)
  = error $ "SBV->C: Cannot compile functions with uninterpreted sorts: " ++ intercalate ", " usorts
  | hasQuants pinfo
  = error "SBV->C: Cannot compile in the presence of quantified variables."
  | not $ null (progSpecialRels pinfo)
  = error "SBV->C: Cannot compile in the presence of special relations."
  | not (null unstructuredDefinitions)
  = error $ "SBV->C: Cannot compile SMT-text-only function definitions: " ++ intercalate ", " unstructuredDefinitions
  | not (null recursiveDefinitions)
  = tbd $ "Recursive or mutually recursive defined functions: " ++ intercalate ", " recursiveDefinitions
  | not (null softConstraints)
  = tbd "Soft constraints"
  | not (null unsupportedConstraintAttributes)
  = tbd $ "Constraint attributes: " ++ intercalate ", " unsupportedConstraintAttributes
  | True
  = ([pre, header, post], requirements)
 where notyet m = error $ "SBV->C: " ++ m ++ " are currently not supported by the C compiler. Please get in touch if you'd like support for this feature!"

       asserts | cgIgnoreAsserts cfg = []
               | True                = origAsserts

       usorts = [s | k@(KADT s _ _) <- Set.toList kindInfo, isUninterpreted k]

       pre    =  text "/* File:" <+> doubleQuotes (nm P.<> text ".c") P.<> text ". Automatically generated by SBV. Do not edit! */"
              $$ text ""

       header = text "#include" <+> doubleQuotes (nm P.<> text ".h")
             $$ (if requires CRequiresLibBF then text "#include <libbf.h>" else empty)

       wideKinds        = wideBVKinds kindInfo
       fpKinds          = arbitraryFPKinds kindInfo
       arrays           = arrayKinds kindInfo
       unsupportedLists = filter (not . listSupported cfg) lists
       unsupportedSets  = filter (not . setSupported cfg) sets
       post   = text ""
             $$ vcat (map codeSeg cgs)
             $$ extDecls
             $$ bitVectorRuntime wideKinds allAssignments
             $$ (if requires CRequiresGMP    then gmpRuntime cfg kindInfo allAssignments else empty)
             $$ (if requires CRequiresLibBF  then arbitraryFPRuntime cfg fpKinds allAssignments else empty)
             $$ (if requires CRequiresNativeFPRounding then nativeFPRuntime else empty)
             $$ (if requires CRequiresText             then textRuntime cfg usesExactInteger else empty)
             $$ adtEqualityRuntimeDecls adts
             $$ (if requires CRequiresLists            then listRuntimeDecls cfg lists else empty)
             $$ (if requires CRequiresSets             then setRuntimeDecls cfg sets else empty)
             $$ (if requires CRequiresLists            then listRuntime cfg usesExactInteger lists else empty)
             $$ (if requires CRequiresSets             then setRuntime cfg sets else empty)
             $$ (if requires CRequiresArrays           then arrayRuntime cfg arrays else empty)
             $$ adtEqualityRuntime cfg adts
             $$ definedFunctionResultRuntime functionResultKinds
             $$ (if null structuredDefinitions then empty else definedFunctionContextType)
             $$ vcat functionPrototypes
             $$ vcat functionDocs
             $$ vcat arrayLambdaDocs
             $$ proto
             $$ text "{"
             $$ text ""
             $$ nest 2 (   gmpStart
                        $$ textStart
                        $$ listStart
                        $$ setStart
                        $$ arrayStart
                        $$ functionResultStart
                        $$ functionContextStart
                        $$ vcat (concatMap (genIO True . (\v -> (isAlive v, v))) inVars)
                        $$ vcat (merge (map (ppTable cfg True consts) tbls) assignmentDocs runtimeChecks)
                        $$ sepIf (not (null assignments) || not (null tbls))
                        $$ vcat (concatMap (genIO False . (True,)) outVars)
                        $$ exactReturn
                        $$ arrayReturn
                        $$ ownedTupleReturn
                        $$ exactADTReturn
                        $$ textReturn
                        $$ listReturn
                        $$ setReturn
                        $$ functionResultEnd
                        $$ arrayEnd
                        $$ setEnd
                        $$ listEnd
                        $$ textEnd
                        $$ gmpEnd
                        $$ normalReturn
                       )
             $$ text "}"
             $$ text ""

       nm = text fn

       assignments = F.toList asgns

       constraints = F.toList cstrs

       softConstraints = [() | (True, _, _) <- constraints]

       unsupportedConstraintAttributes = nub [attribute
                                              | (_, attributes, _) <- constraints
                                              , (attribute, _) <- attributes
                                              , attribute /= ":named"
                                              ]

       runtimeChecks = map genAssert asserts ++ map genConstraint constraints

       functionNames = [(T.pack functionName, CTypes.definedFunctionCName functionName) | (functionName, _) <- definitions]

       structuredDefinitions = [ (functionName, resultKind, dependencies, functionType, lambdaInfo)
                               | (functionName, (definition@(SMTDef resultKind dependencies _ _), functionType)) <- definitions
                               , Just lambdaInfo <- [smtDefInfo definition]
                               ]

       unstructuredDefinitions = [ functionName
                                 | (functionName, (definition, _)) <- definitions
                                 , Nothing <- [smtDefInfo definition]
                                 ]

       definitionNames      = Set.fromList (map fst definitions)
       definitionComponents = DG.stronglyConnComp
                                [ (functionName, functionName, filter (`Set.member` definitionNames) dependencies)
                                | (functionName, (SMTDef _ dependencies _ _, _)) <- definitions
                                ]
       recursiveDefinitions = concat [functionGroup | DG.CyclicSCC functionGroup <- definitionComponents]

       arrayLambdaDefinitions = [ (sv, lambdaInfo)
                                | (sv, SBVApp (ArrayInit (Right lambdaDef)) []) <- assignments
                                , Just lambdaInfo <- [smtLambdaInfo lambdaDef]
                                ]

       functionAssignments    = concatMap (\(_, _, _, _, lambdaInfo) -> F.toList (liAssignments lambdaInfo)) structuredDefinitions
       arrayLambdaAssignments = concatMap (F.toList . liAssignments . snd) arrayLambdaDefinitions
       lambdaAssignments      = functionAssignments ++ arrayLambdaAssignments
       allAssignments         = assignments ++ lambdaAssignments

       functionPrototypes  = [ definedFunctionSignature functionName resultKind (liParams lambdaInfo) P.<> semi
                             | (functionName, resultKind, _, _, lambdaInfo) <- structuredDefinitions
                             ]

       generatedFunctions  = [ ppDefinedFunction cfg adts functionNames functionName resultKind functionType lambdaInfo
                             | (functionName, resultKind, _, functionType, lambdaInfo) <- structuredDefinitions
                             ]
       functionDocs        = map fst generatedFunctions

       functionResultKinds = nub [ resultKind
                                 | (_, resultKind, _, _, _) <- structuredDefinitions
                                 , definedFunctionResultNeedsClone cfg adts resultKind
                                 ]

       generatedArrayLambdas = map (uncurry (ppArrayLambda cfg adts functionNames)) arrayLambdaDefinitions
       arrayLambdaDocs        = map fst generatedArrayLambdas

       generatedAssignments = map genAsgn assignments
       assignmentDocs        = [(location, doc) | (location, doc, _) <- generatedAssignments]

       requirements = Set.unions
         [ kindRequirements
         , Set.unions [needed | (_, _, needed) <- generatedAssignments]
         , Set.unions (map snd generatedFunctions)
         , Set.unions (map snd generatedArrayLambdas)
         , Set.unions [operationRequirements cfg (op, kindOf sv) | (sv, SBVApp op _) <- assignments]
         ]

       kindRequirements = Set.fromList $
            [CRequiresWideBV | not (null wideKinds)]
         ++ [CRequiresLibBF  | not (null fpKinds)]
         ++ [CRequiresLibM   | not (null fpKinds)]
         ++ [CRequiresGMP    | usesGMP]
         ++ [CRequiresText   | KString `Set.member` kindInfo || KChar `Set.member` kindInfo]
         ++ [CRequiresLists  | not (null lists)]
         ++ [CRequiresSets   | not (null sets)]
         ++ [CRequiresArrays | not (null arrays)]

       requires requirement = requirement `Set.member` requirements

       usesGMP          = any (isExactGMPKind cfg) kindInfo
       usesExactInteger = isExactGMPKind cfg KUnbounded && KUnbounded `Set.member` kindInfo

       containsNestedList = containsUnsupportedCollection isList

       containsNestedSet = containsUnsupportedCollection isSet

       containsUnsupportedCollection isCollection = walk Set.empty
        where walk _ kind
                | isCollection kind
                = False
              walk visited (KTuple fields)
                = any (walk visited) fields
              walk visited (KList elementKind)
                = walk visited elementKind
              walk visited (KSet elementKind)
                = walk visited elementKind
              walk visited (KArray keyKind valueKind)
                = walk visited keyKind || walk visited valueKind
              walk visited kind
                | isADT kind
                , not (isRoundingMode kind)
                , not (isUninterpreted kind)
                =    not (kind `Set.member` visited)
                  && any (any (walk (Set.insert kind visited)) . snd) (adtConstructors adts kind)
              walk _ kind
                = any isCollection (expandKinds kind)

       assignmentUsesText (sv, SBVApp _ arguments) = any ((`elem` [KChar, KString]) . kindOf) (sv : arguments)

       assignmentUsesList (sv, SBVApp _ arguments) = any (isList . kindOf) (sv : arguments)

       assignmentUsesSet (sv, SBVApp _ arguments) = any (isSet . kindOf) (sv : arguments)

       listElementKind (KList elementKind) = elementKind
       listElementKind kind                = die $ "Expected a list kind, received " ++ show kind

       setElementKind (KSet elementKind) = elementKind
       setElementKind kind               = die $ "Expected a set kind, received " ++ show kind

       gmpStart
         | requires CRequiresGMP = gmpContextStart
         | True                     = empty
       gmpEnd
         | requires CRequiresGMP = gmpContextEnd
         | True                     = empty

       textStart
         | requires CRequiresText = textContextStart
         | True                    = empty
       textEnd
         | requires CRequiresText = textContextEnd
         | True                    = empty

       listStart
         | requires CRequiresLists = listContextStart
         | True                    = empty
       listEnd
         | requires CRequiresLists = listContextEnd
         | True                    = empty

       setStart
         | requires CRequiresSets = setContextStart
         | True                   = empty
       setEnd
         | requires CRequiresSets = setContextEnd
         | True                   = empty

       arrayStart
         | requires CRequiresArrays = arrayContextStart
         | True                     = empty

       arrayEnd
         | requires CRequiresArrays = arrayContextEnd
         | True                     = empty

       functionContextStart
         | null structuredDefinitions = empty
         | True                       = definedFunctionContextInitialization requirements

       functionResultStart
         | requires CRequiresFunctionResults = text "sbv_function_result_ctx __sbv_function_result_ctx = {NULL};"
         | True                               = empty

       functionResultEnd
         | requires CRequiresFunctionResults = text "sbv_function_result_ctx_end(&__sbv_function_result_ctx);"
         | True                               = empty

       exactReturn = case mbRet of
                       Just sv | isExactGMPKind cfg (kindOf sv)
                               -> gmpSet (kindOf sv) (text "__result") (showSV cfg consts sv) P.<> semi
                       _       -> empty

       arrayReturn = case mbRet of
                       Just sv | isArray sv
                               -> text "const" <+> text (arrayOutputCType (kindOf sv)) <+> text "__result" <+> text "="
                                  <+> text (arrayExportName (kindOf sv)) P.<> parens (showSV cfg consts sv) P.<> semi
                       _       -> empty

       ownedTupleReturn = case mbRet of
                            Just sv
                              | tupleNeedsOwnership cfg (kindOf sv)
                              -> text "const" <+> text (tupleCType (kindOf sv)) <+> text "__result" <+> text "="
                                 <+> text (tupleOwnedCloneName (kindOf sv)) P.<> parens (showSV cfg consts sv) P.<> semi
                            _ -> empty

       exactADTReturn = case mbRet of
                          Just sv
                            | isOwnedADT cfg adts sv
                            -> text "const" <+> text (adtCType (kindOf sv)) <+> text "__result" <+> text "="
                           <+> text (adtOwnedCloneName (kindOf sv))
                                 P.<> parens (showSV cfg consts sv)
                                 P.<> semi
                          _ -> empty

       textReturn = case mbRet of
                      Just sv | kindOf sv == KString
                              -> text "const SString __result =" <+> textClone (showSV cfg consts sv) P.<> semi
                      _       -> empty

       listReturn = case mbRet of
                      Just sv | isList sv
                              -> text "const" <+> text (listCType (kindOf sv)) <+> text "__result ="
                              <+> listClone (kindOf sv) (showSV cfg consts sv) P.<> semi
                      _       -> empty

       setReturn = case mbRet of
                     Just sv | isSet sv
                             -> text "const" <+> text (setCType (kindOf sv)) <+> text "__result ="
                             <+> setClone (kindOf sv) (showSV cfg consts sv) P.<> semi
                     _       -> empty

       normalReturn = case mbRet of
                        Just sv | isArray sv                           -> text "return __result;"
                        Just sv | tupleNeedsOwnership cfg (kindOf sv) -> text "return __result;"
                        Just sv | isOwnedADT cfg adts sv               -> text "return __result;"
                        Just sv | kindOf sv == KString                 -> text "return __result;"
                        Just sv | isList sv                            -> text "return __result;"
                        Just sv | isSet sv                             -> text "return __result;"
                        Just sv | not (isExactGMPKind cfg (kindOf sv)) -> mkRet sv
                        _                                             -> empty

       codeSeg (fnm, ls) =  text "/* User specified custom code for" <+> doubleQuotes (text fnm) <+> text "*/"
                         $$ vcat (map text ls)
                         $$ text ""

       ins = case topInps of
               ResultTopInps (is, []) -> is
               ResultTopInps is       -> die $ "Unexpected trackers: " ++ show is
               ResultLamInps is       -> die $ "Unexpected inputs  : " ++ show is

       typeWidth = getMax 0 $ [len (kindOf s) | (s, _) <- assignments] ++ [len (kindOf s) | NamedSymVar s _ <- ins]
                where len (KVar s)           = die $ "Variable: " ++ s
                      len KReal{}            = 5
                      len KFloat{}           = 6 -- SFloat
                      len KDouble{}          = 7 -- SDouble
                      len KString{}          = 7 -- SString
                      len KChar{}            = 5 -- SChar
                      len k@KList{}          = length (listCType k)
                      len k@KSet{}           = length (setCType k)
                      len KUnbounded{}       = 8
                      len KBool              = 5 -- SBool
                      len (KBounded False n) = 5 + length (show n) -- SWordN
                      len (KBounded True  n) = 4 + length (show n) -- SIntN
                      len KRational{}        = length "SRational"
                      len (KFP eb sb)         = 6 + length (show eb) + length (show sb)
                      len k@KArray{}         = length (arrayCType k)
                      len k@KTuple{}         = length (tupleCType k)
                      len (KApp s _)         = die $ "Uninterpreted ADT app: " ++ s
                      len k@(KADT s _ _)
                        | isRoundingMode k = length (show k)
                        | isUninterpreted k = die $ "Uninterpreted ADT: " ++ s
                        | True             = length (adtCType k)

                      getMax 8 _      = 8  -- Preserve the historical declaration layout once native-width alignment is reached.
                      getMax m []     = m
                      getMax m (x:xs) = getMax (m `max` x) xs

       consts = (falseSV, falseCV) : (trueSV, trueCV) : preConsts

       -- TODO: The following is brittle. We should really have a function elsewhere
       -- that walks the SBVExprs and collects the SWs together.
       usedVariables = Set.unions (retSWs : checkSWs : map usedCgVal outVars ++ map usedAsgn assignments)
         where retSWs   = maybe Set.empty Set.singleton mbRet
               checkSWs = Set.fromList ([sv | (_, _, sv) <- constraints] ++ [sv | (_, _, sv) <- asserts])

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
       genIO True  (alive, (cNm, CgAtomic sv))
         | isArray sv = [statement | alive, statement <- arrayInputSetup typeWidth sv cNm]
         | isSet sv   = [declSV typeWidth sv <+> text "=" <+> setNormalize (kindOf sv) (text cNm) P.<> semi | alive]
         | True       = [declSV typeWidth sv <+> text "=" <+> inputValue cNm sv P.<> semi | alive]
       genIO False (alive, (cNm, CgAtomic sv))
         | isArray sv                          = [text "*" P.<> text cNm <+> text "=" <+> text (arrayExportName (kindOf sv)) P.<> parens (showSV cfg consts sv) P.<> semi | alive]
         | isExactGMPKind cfg (kindOf sv)      = [gmpSet (kindOf sv) (text cNm) (showSV cfg consts sv) P.<> semi | alive]
         | kindOf sv == KString                = [text "*" P.<> text cNm <+> text "=" <+> textClone (showSV cfg consts sv) P.<> semi | alive]
         | isList sv                           = [text "*" P.<> text cNm <+> text "=" <+> listClone (kindOf sv) (showSV cfg consts sv) P.<> semi | alive]
         | isSet sv                            = [text "*" P.<> text cNm <+> text "=" <+> setClone (kindOf sv) (showSV cfg consts sv) P.<> semi | alive]
         | tupleNeedsOwnership cfg (kindOf sv) = [text "*" P.<> text cNm <+> text "=" <+> text (tupleOwnedCloneName (kindOf sv)) P.<> parens (showSV cfg consts sv) P.<> semi | alive]
         | isOwnedADT cfg adts sv              = [ text "*" P.<> text cNm <+> text "="
                                               <+> text (adtOwnedCloneName (kindOf sv))
                                                     P.<> parens (showSV cfg consts sv)
                                                     P.<> semi
                                                 | alive
                                                 ]
         | True                                = [text "*" P.<> text cNm <+> text "=" <+> showSV cfg consts sv P.<> semi | alive]
       genIO isInp (_,     (cNm, CgArray sws)) = zipWith genElt sws [(0::Int)..]
         where genElt sv i
                 | isInp                         = declSV typeWidth sv <+> text "=" <+> inputValue entry sv P.<> semi
                 | isExactGMPKind cfg kind      = gmpSet kind (text entry) value P.<> semi
                 | isArray kind                 = text entry <+> text "=" <+> text (arrayExportName kind) P.<> parens value P.<> semi
                 | kind == KString              = text entry <+> text "=" <+> textClone value P.<> semi
                 | isList kind                  = text entry <+> text "=" <+> listClone kind value P.<> semi
                 | isSet kind                   = text entry <+> text "=" <+> setClone kind value P.<> semi
                 | tupleNeedsOwnership cfg kind = text entry <+> text "=" <+> text (tupleOwnedCloneName kind) P.<> parens value P.<> semi
                 | isOwnedADT cfg adts sv        = text entry <+> text "=" <+> text (adtOwnedCloneName kind) P.<> parens value P.<> semi
                 | True                         = text entry <+> text "=" <+> value P.<> semi
                 where entry = cNm ++ "[" ++ show i ++ "]"
                       kind  = kindOf sv
                       value = showSV cfg consts sv

       inputValue cNm sv
         | isWideBV k = wideBVNormalize k (text cNm)
         | isFP k      = arbitraryFPNormalize k (text cNm)
         | True        = text cNm
         where k = kindOf sv

       mkRet sv = text "return" <+> showSV cfg consts sv P.<> semi

       genAsgn :: (SV, SBVExpr) -> (Int, Doc, Set.Set CRequirement)
       genAsgn (sv, n) = (cLocation consts sv, doc, needed)
         where (doc, needed) = ppExpr cfg adts functionNames consts n sv (declSV typeWidth sv) (declSVNoConst typeWidth sv)

       -- merge tables intermixed with assignments and assertions, paying attention to putting tables as
       -- early as possible and tables right after.. Note that the assignment list (second argument) is sorted on its order
       merge :: [(Int, Doc)] -> [(Int, Doc)] -> [(Int, Doc)] -> [Doc]
       merge tables asgnments asrts = map snd $ mergeLocated asrts (mergeLocated tables asgnments)

       genAssert (msg, cs, sv) = (cLocation consts sv, doc)
         where doc =     text "/* ASSERTION:" <+> text msg
                     $$  maybe empty (vcat . map text) (locInfo (getCallStack <$> cs))
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

       genConstraint (_, attributes, sv) = (cLocation consts sv, doc)
         where doc =  text "/* CONSTRAINT */"
                   $$ text "if" P.<> parens (text "!" P.<> parens (showSV cfg consts sv))
                   $$ text "{"
                   $+$ nest 2 (vcat [errOut, text "exit(-1);"])
                   $$ text "}"
                   $$ text ""

               description = fromMaybe "unnamed" (lookup ":named" attributes)

               errOut = text "fprintf" P.<> parens (fsep (punctuate comma [ text "stderr"
                                                                          , cStringLiteral "%s:%d:CONSTRAINT FAILED: %s\n"
                                                                          , text "__FILE__"
                                                                          , text "__LINE__"
                                                                          , cStringLiteral description
                                                                          ])) P.<> semi

-- | Return the source-order location used to interleave a value's dependent
-- declarations. Constants are available before every generated assignment.
cLocation :: [(SV, CV)] -> SV -> Int
cLocation constants sv@(SV _ (NodeId (_, _, nodeIndex)))
  | isJust (lookup sv constants) = -1
  | True                         = nodeIndex

-- | Render one finite lookup table at the point where all its elements are
-- available. Constant top-level tables may use static storage; lambda-local
-- tables always use automatic storage so their entries may depend on parameters.
ppTable :: CgConfig -> Bool -> [(SV, CV)] -> ((Int, Kind, Kind), [SV]) -> (Int, Doc)
ppTable cfg allowStatic constants ((tableIndex, _, resultKind), elements)
  = (location, storage <+> text "const" <+> text tableElementType <+> tableName P.<> text "[] = {"
              $$ nest 4 (fsep (punctuate comma (align (map renderElement elements))))
              $$ text "};")
 where location = maximum (-1 : map (cLocation constants) elements)
       renderElement element = arrayStoredValue resultKind (showSV cfg constants element)
       tableElementType
         | isArray resultKind = CTypes.elementCType resultKind
         | True               = showCType resultKind
       storage
         | allowStatic && location == -1 && not (tableMustBeLocal cfg resultKind) = text "static"
         | True                                                                  = empty
       tableName = text ("table" ++ show tableIndex)

-- | Merge two source-ordered declaration streams. Entries from the right-hand
-- stream precede left-hand entries at the same location, allowing a table to
-- follow the assignment that computes its final element.
mergeLocated :: [(Int, Doc)] -> [(Int, Doc)] -> [(Int, Doc)]
mergeLocated []               right                       = right
mergeLocated left             []                          = left
mergeLocated left@((i, x):xs) right@((j, y):ys)
  | i < j = (i, x) : mergeLocated xs right
  | True  = (j, y) : mergeLocated left ys

-- | Render arbitrary text as a UTF-8 C string literal, using fixed-width
-- octal escapes where a byte cannot safely appear verbatim.
cStringLiteral :: String -> Doc
cStringLiteral = doubleQuotes . text . concatMap escapeByte . BS.unpack . TE.encodeUtf8 . T.pack
 where escapeByte byte
         | byte == 34              = "\\\""
         | byte == 63              = "\\?"
         | byte == 92              = "\\\\"
         | 32 <= byte, byte <= 126 = [chr (fromIntegral byte)]
         | True                    = '\\' : replicate (3 - length octal) '0' ++ octal
         where octal = showOct byte ""

-- | Declare the private bundle of ownership-arena pointers threaded through
-- calls between generated SBV functions.
definedFunctionContextType :: Doc
definedFunctionContextType = text $ unlines
  [ "typedef struct {"
  , "  void *gmp;"
  , "  void *text;"
  , "  void *list;"
  , "  void *set;"
  , "  void *array;"
  , "  void *function_result;"
  , "} sbv_function_ctx;"
  , ""
  ]

-- | Initialize a private function-context bundle from the ownership arenas
-- available in the surrounding generated function.
definedFunctionContextInitialization :: Set.Set CRequirement -> Doc
definedFunctionContextInitialization requirements
  = text "sbv_function_ctx __sbv_function_ctx =" <+> braces (fsep (punctuate comma fields)) P.<> semi
 where fields = [ field CRequiresGMP             "gmp"             "__sbv_gmp_ctx"
                , field CRequiresText            "text"            "__sbv_text_ctx"
                , field CRequiresLists           "list"            "__sbv_list_ctx"
                , field CRequiresSets            "set"             "__sbv_set_ctx"
                , field CRequiresArrays          "array"           "__sbv_array_ctx"
                , field CRequiresFunctionResults "function_result" "__sbv_function_result_ctx"
                ]

       field requirement fieldName contextName
         = text ("." ++ fieldName ++ " =") <+> if requirement `Set.member` requirements
                                                   then text ("&" ++ contextName)
                                                   else text "NULL"

-- | Test whether a private function result needs a stable deep copy because
-- its by-value representation contains independently owned aggregate storage.
definedFunctionResultNeedsClone :: CgConfig -> [Kind] -> Kind -> Bool
definedFunctionResultNeedsClone cfg adts kind
  | KTuple{} <- kind          = tupleNeedsOwnership cfg kind
  | isConcreteADTKind kind    = adtNeedsOwnership cfg adts kind
  | True                      = False

-- | Return the generated helper name that clones one private aggregate result
-- into the shared function-result arena.
definedFunctionResultCloneName :: Kind -> String
definedFunctionResultCloneName kind = "sbv_function_result_clone_" ++ CTypes.kindTag kind

-- | Render a deep clone into the shared private function-result arena.
definedFunctionResultClone :: Kind -> Doc -> Doc
definedFunctionResultClone kind value
  = text (definedFunctionResultCloneName kind)
      P.<> parens (fsep (punctuate comma [text "&__sbv_function_result_ctx", value]))

-- | Emit temporary ownership storage for aggregate values returned by private
-- generated functions. The public boundary clones these values once more
-- before this arena is released.
definedFunctionResultRuntime :: [Kind] -> Doc
definedFunctionResultRuntime []    = empty
definedFunctionResultRuntime kinds = text . unlines $
     [ "/* Stable storage for owned aggregate results of private SBV functions. */"
     , "typedef void (*sbv_function_result_release)(void *);"
     , "typedef struct sbv_function_result_node {"
     , "  struct sbv_function_result_node *next;"
     , "  void *value;"
     , "  sbv_function_result_release release;"
     , "} sbv_function_result_node;"
     , "typedef struct { sbv_function_result_node *head; } sbv_function_result_ctx;"
     , ""
     , "static SBV_CGEN_UNUSED void sbv_function_result_ctx_remember(sbv_function_result_ctx *ctx, void *value, sbv_function_result_release release)"
     , "{"
     , "  sbv_function_result_node *node = (sbv_function_result_node *) malloc(sizeof(*node));"
     , "  if (ctx == NULL || value == NULL || release == NULL || node == NULL) abort();"
     , "  node->next = ctx->head;"
     , "  node->value = value;"
     , "  node->release = release;"
     , "  ctx->head = node;"
     , "}"
     , ""
     , "static SBV_CGEN_UNUSED void sbv_function_result_ctx_end(sbv_function_result_ctx *ctx)"
     , "{"
     , "  while (ctx->head != NULL) {"
     , "    sbv_function_result_node *node = ctx->head;"
     , "    ctx->head = node->next;"
     , "    node->release(node->value);"
     , "    free(node);"
     , "  }"
     , "}"
     , ""
     ]
  ++ concatMap helpers kinds
 where helpers kind =
         [ "static SBV_CGEN_UNUSED void " ++ releaseName ++ "(void *opaque)"
         , "{"
         , "  " ++ cType ++ " *value = (" ++ cType ++ " *) opaque;"
         , "  " ++ ownedReleaseName kind ++ "(value);"
         , "  free(value);"
         , "}"
         , ""
         , "static SBV_CGEN_UNUSED " ++ cType ++ " " ++ cloneName ++ "(sbv_function_result_ctx *ctx, " ++ cType ++ " value)"
         , "{"
         , "  " ++ cType ++ " *result = (" ++ cType ++ " *) malloc(sizeof(*result));"
         , "  if (result == NULL) abort();"
         , "  *result = " ++ ownedCloneName kind ++ "(value);"
         , "  sbv_function_result_ctx_remember(ctx, result, " ++ releaseName ++ ");"
         , "  return *result;"
         , "}"
         , ""
         ]
        where cType       = showCType kind
              cloneName   = definedFunctionResultCloneName kind
              releaseName = "sbv_function_result_release_" ++ CTypes.kindTag kind

       ownedCloneName kind@KTuple{} = tupleOwnedCloneName kind
       ownedCloneName kind
         | isConcreteADTKind kind    = adtOwnedCloneName kind
       ownedCloneName kind           = die $ "Expected an owned tuple or ADT result, received " ++ show kind

       ownedReleaseName kind@KTuple{} = tupleOwnedReleaseName kind
       ownedReleaseName kind
         | isConcreteADTKind kind      = adtOwnedReleaseName kind
       ownedReleaseName kind           = die $ "Expected an owned tuple or ADT result, received " ++ show kind

-- | Render the private C signature shared by a defined function's prototype
-- and implementation.
definedFunctionSignature :: String -> Kind -> [(Quantifier, SV)] -> Doc
definedFunctionSignature originalName resultKind parameters
  = text "static" <+> text (showCType resultKind) <+> text (CTypes.definedFunctionCName originalName)
      P.<> parens renderedParameters
 where renderedParameters = fsep . punctuate comma $
           text "sbv_function_ctx *const __sbv_parent_function_ctx"
         : [text "const" <+> text (showCType parameter) <+> text (show parameter) | (_, parameter) <- parameters]

-- | Lower one non-recursive, first-order SBV function definition from its
-- retained expression DAG. Nested lambdas and higher-order callbacks are
-- handled by a later lowering stage.
ppDefinedFunction :: CgConfig -> [Kind] -> [(T.Text, String)] -> String -> Kind -> SBVType -> LambdaInfo -> (Doc, Set.Set CRequirement)
ppDefinedFunction cfg adts functionNames originalName declaredResultKind (SBVType signatureKinds)
                  LambdaInfo{ liAssignments = functionProgram
                            , liParams      = parameters
                            , liOutput      = functionOutput
                            , liConsts      = constants
                            , liTables      = tables
                            }
  | null signatureKinds
  = die $ "Empty type for defined function " ++ show originalName
  | declaredResultKind /= resultKind
  = die $ "Result-kind mismatch in defined function " ++ show originalName
  | map (kindOf . snd) parameters /= parameterKinds
  = die $ "Parameter-kind mismatch in defined function " ++ show originalName
  | any ((/= ALL) . fst) parameters
  = die $ "Non-universal parameter in defined function " ++ show originalName
  | kindOf functionOutput /= resultKind
  = die $ "Output-kind mismatch in defined function " ++ show originalName
  | not (null nestedLambdas)
  = tbd $ "Nested lambdas in defined function " ++ show originalName
  | not (null unsupportedManagedKinds)
  = tbd $ "Managed values in defined function " ++ show originalName ++ ": " ++ intercalate ", " (map show unsupportedManagedKinds)
  | True
  = (functionDoc, functionRequirements)
 where (parameterKinds, resultKind) = (init signatureKinds, last signatureKinds)
       assignments                  = F.toList functionProgram
       functionConsts               = (falseSV, falseCV) : (trueSV, trueCV) : constants
       functionValues               = functionOutput : map snd parameters ++ map fst assignments ++ map fst constants
       typeWidth                    = maximum (0 : map (length . showCType) functionValues)
       nestedLambdas                = [sv | (sv, SBVApp (ArrayInit (Right _)) _) <- assignments]
       unsupportedManagedKinds      = nub [ kind
                                          | value <- functionValues
                                          , let kind = kindOf value
                                          , functionValueHasUnsupportedManagedStorage kind
                                          ]

       functionValueHasUnsupportedManagedStorage kind
         | isExactGMPKind cfg kind = False
         | kind == KString         = False
         | isList kind             = False
         | isSet kind              = False
         | isArray kind            = False
         | KTuple fields <- kind   = any functionValueHasUnsupportedManagedStorage fields
         | isConcreteADTKind kind  = False
         | True                    = valueNeedsOwnership cfg kind

       generatedTables = map (ppTable cfg False functionConsts) tables

       generatedAssignments = [(cLocation functionConsts sv, doc, needed)
                              | (sv, expression) <- assignments
                              , let (doc, needed) = ppExpr cfg adts functionNames functionConsts expression sv
                                                         (declSV typeWidth sv) (declSVNoConst typeWidth sv)
                              ]

       assignmentDocs = [(location, doc) | (location, doc, _) <- generatedAssignments]

       functionRequirements = Set.unions
         [ Set.fromList $ [CRequiresGMP             | any (isExactGMPKind cfg) expandedFunctionKinds]
                       ++ [CRequiresText            | KString `elem` expandedFunctionKinds]
                       ++ [CRequiresLists           | any isList expandedFunctionKinds]
                       ++ [CRequiresSets            | any isSet expandedFunctionKinds]
                       ++ [CRequiresArrays          | any isArray expandedFunctionKinds]
                       ++ [CRequiresFunctionResults | definedFunctionResultNeedsClone cfg adts resultKind]
         , Set.unions [needed | (_, _, needed) <- generatedAssignments]
         , Set.unions [operationRequirements cfg (op, kindOf sv) | (sv, SBVApp op _) <- assignments]
         ]

       expandedFunctionKinds = concatMap (expandKinds . kindOf) functionValues

       contextSetup
         =  setupContext CRequiresGMP             "sbv_gmp_ctx"             "gmp"
         $$ setupContext CRequiresText            "sbv_text_ctx"            "text"
         $$ setupContext CRequiresLists           "sbv_list_ctx"            "list"
         $$ setupContext CRequiresSets            "sbv_set_ctx"             "set"
         $$ setupContext CRequiresArrays          "sbv_array_ctx"           "array"
         $$ setupContext CRequiresFunctionResults "sbv_function_result_ctx" "function_result"
         $$ text "sbv_function_ctx __sbv_function_ctx = *__sbv_parent_function_ctx;"
         $$ bindContext CRequiresGMP             "gmp"
         $$ bindContext CRequiresText            "text"
         $$ bindContext CRequiresLists           "list"
         $$ bindContext CRequiresSets            "set"
         $$ bindContext CRequiresArrays          "array"
         $$ bindContext CRequiresFunctionResults "function_result"

       setupContext requirement contextType fieldName
         | requirement `Set.member` functionRequirements
         =  text contextType <+> text ("*__sbv_parent_" ++ fieldName ++ "_ctx = (" ++ contextType ++ " *) __sbv_parent_function_ctx->" ++ fieldName ++ ";")
         $$ text contextType <+> text ("__sbv_" ++ fieldName ++ "_ctx = *__sbv_parent_" ++ fieldName ++ "_ctx;")
         | True
         = empty

       bindContext requirement fieldName
         | requirement `Set.member` functionRequirements
         = text ("__sbv_function_ctx." ++ fieldName ++ " = &__sbv_" ++ fieldName ++ "_ctx;")
         | True
         = empty

       contextCommit
         =  commitContext CRequiresGMP             "gmp"
         $$ commitContext CRequiresText            "text"
         $$ commitContext CRequiresLists           "list"
         $$ commitContext CRequiresSets            "set"
         $$ commitContext CRequiresArrays          "array"
         $$ commitContext CRequiresFunctionResults "function_result"

       commitContext requirement fieldName
         | requirement `Set.member` functionRequirements
         = text ("*__sbv_parent_" ++ fieldName ++ "_ctx = __sbv_" ++ fieldName ++ "_ctx;")
         | True
         = empty

       functionDoc
         = definedFunctionSignature originalName resultKind parameters
          $$ text "{"
          $$ nest 2 (   contextSetup
                     $$ vcat (map snd (mergeLocated generatedTables assignmentDocs))
                     $$ text "const" <+> text (showCType resultKind) <+> text "__sbv_function_result =" <+> functionResult P.<> semi
                     $$ contextCommit
                     $$ text "return __sbv_function_result;"
                    )
          $$ text "}"
          $$ text ""

       functionResult
         | definedFunctionResultNeedsClone cfg adts resultKind
         = definedFunctionResultClone resultKind (showSV cfg functionConsts functionOutput)
         | True
         = showSV cfg functionConsts functionOutput

-- | Lower a retained one-argument array lambda into a C lookup callback. Its
-- local DAG uses the ordinary scalar lowering pipeline, so wide bit-vectors,
-- floating-point values, exact numbers, and finite tables retain their usual
-- semantics.
ppArrayLambda :: CgConfig -> [Kind] -> [(T.Text, String)] -> SV -> LambdaInfo -> (Doc, Set.Set CRequirement)
ppArrayLambda cfg adts functionNames arraySV lambdaInfo@LambdaInfo{ liAssignments = lambdaPgm
                                                                 , liParams      = parameters
                                                                 , liOutput      = lambdaOutput
                                                                 , liConsts      = constants
                                                                 , liTables      = tables
                                                                 }
  = case (kindOf arraySV, parameters) of
      (KArray keyKind valueKind, [(ALL, parameter)])
        | kindOf parameter /= keyKind
        -> die $ "Array-lambda parameter kind " ++ show (kindOf parameter) ++ " does not match " ++ show keyKind
        | kindOf lambdaOutput /= valueKind
        -> die $ "Array-lambda result kind " ++ show (kindOf lambdaOutput) ++ " does not match " ++ show valueKind
        | not (null nestedLambdas)
        -> tbd "Nested structured lambdas inside lambda arrays"
        | not (null definedFunctionCalls)
        -> tbd "Defined SBV functions inside structured lambda arrays"
        | lambdaResultNeedsManagedStorage valueKind
        -> tbd "Structured lambda arrays returning managed aggregate values"
        | True
        -> (helper keyKind valueKind parameter, requirements)
      (KArray{}, _) -> die $ "Expected exactly one universal array-lambda parameter, received " ++ show parameters
      (kind, _)     -> die $ "Expected an array-valued lambda node, received " ++ show kind
 where assignments = F.toList lambdaPgm
       lambdaConsts = (falseSV, falseCV) : (trueSV, trueCV) : constants
       lambdaValues = lambdaOutput : map snd parameters ++ map fst assignments ++ map fst constants
       typeWidth    = maximum (0 : map (length . showCType) lambdaValues)
       usesGMP      = arrayLambdaUsesGMP cfg lambdaInfo

       nestedLambdas = [sv | (sv, SBVApp (ArrayInit (Right _)) _) <- assignments]
       definedFunctionCalls = [ symbol
                              | (_, SBVApp (Uninterpreted symbol) _) <- assignments
                              , isJust (lookup symbol functionNames)
                              ]

       lambdaResultNeedsManagedStorage KString         = True
       lambdaResultNeedsManagedStorage KList{}         = True
       lambdaResultNeedsManagedStorage KSet{}          = True
       lambdaResultNeedsManagedStorage (KTuple fields) = any lambdaResultNeedsManagedStorage fields
       lambdaResultNeedsManagedStorage kind
         | isConcreteADTKind kind = adtNeedsOwnership cfg adts kind
         | True                   = False

       generatedTables = map (ppTable cfg False lambdaConsts) tables

       generatedAssignments = [(cLocation lambdaConsts sv, doc, needed)
                              | (sv, expression) <- assignments
                              , let (doc, needed) = ppExpr cfg adts functionNames lambdaConsts expression sv
                                                         (declSV typeWidth sv) (declSVNoConst typeWidth sv)
                              ]

       assignmentDocs = [(location, doc) | (location, doc, _) <- generatedAssignments]

       requirements = Set.unions
         [ Set.unions [needed | (_, _, needed) <- generatedAssignments]
         , Set.unions [operationRequirements cfg (op, kindOf sv) | (sv, SBVApp op _) <- assignments]
         , if usesGMP then Set.singleton CRequiresGMP else Set.empty
         ]

       helper keyKind valueKind parameter
         = text "static" <+> text (showCType valueKind) <+> text (arrayLambdaName arraySV)
             P.<> parens (fsep (punctuate comma [text "const void *context", text (showCType keyKind) <+> text (show parameter)]))
          $$ text "{"
          $$ nest 2 (   contextSetup
                     $$ vcat (map snd (mergeLocated generatedTables assignmentDocs))
                     $$ text "const" <+> text (showCType valueKind) <+> text "__sbv_lambda_result" <+> text "=" <+> showSV cfg lambdaConsts lambdaOutput P.<> semi
                     $$ contextCommit
                     $$ text "return __sbv_lambda_result;"
                    )
          $$ text "}"
          $$ text ""

       contextSetup
         | usesGMP =  text "sbv_gmp_ctx *__sbv_gmp_parent_ctx = (sbv_gmp_ctx *) context;"
                   $$ text "sbv_gmp_ctx __sbv_gmp_ctx = *__sbv_gmp_parent_ctx;"
         | True    = parens (text "void") <+> text "context" P.<> semi

       contextCommit
         | usesGMP = text "*__sbv_gmp_parent_ctx = __sbv_gmp_ctx;"
         | True    = empty

-- | Test whether a kind is a concrete user ADT rather than a built-in or
-- uninterpreted sort.
isConcreteADTKind :: Kind -> Bool
isConcreteADTKind KApp{} = True
isConcreteADTKind kind   = isADT kind && not (isRoundingMode kind) && not (isUninterpreted kind)

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
        cvt FP_ObjEqual          = dispatch $ same $ \_ [a, b] -> nativeFPObjectEqual a b
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
                   ((m, _):args)
                     | isRoundingMode m -> case checkRM (m `lookup` consts) of
                                             Nothing          -> args
                                             Just (Left  msg) -> die msg
                                             Just (Right msg) -> tbd msg
                     | True              -> as

        -- Check that the RM is RoundNearestTiesToEven.
        -- If we start supporting other rounding-modes, this would be the point where we'd insert the rounding-mode set/reset code
        -- instead of merely returning OK or not
        checkRM (Just cv@(CV k v))
          | k == kRoundingMode = case v of
                                   CADT ("RoundNearestTiesToEven", []) -> Nothing
                                   CADT (s,                        []) -> Just (Right $ "handleIEEE: Unsupported rounding-mode: " ++ show s ++ " for: " ++ show w)
                                   _                                   -> Just (Left  $ "handleIEEE: Unexpected value for rounding-mode: " ++ show cv ++ " for: " ++ show w)
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
        wrapMinMax k a b s = parens cond <+> text "?" <+> fzero <+> text ":" <+> s
          where fzero = text $ if k == KFloat then showCFloat 0 else showCDouble 0
                cond  =                   parens (text "FP_ZERO == fpclassify" P.<> parens a)                                  -- a is zero
                        <+> text "&&" <+> parens (text "FP_ZERO == fpclassify" P.<> parens b)                                  -- b is zero
                        <+> text "&&" <+> parens (text "signbit" P.<> parens a <+> text "!=" <+> text "signbit" P.<> parens b) -- a and b differ in sign

-- | Lower and render one symbolic assignment together with the facilities it
-- requires from the generated C translation unit.
ppExpr :: CgConfig -> [Kind] -> [(T.Text, String)] -> [(SV, CV)] -> SBVExpr -> SV -> Doc -> (Doc, Doc) -> (Doc, Set.Set CRequirement)
ppExpr cfg adts functionNames consts (SBVApp op opArgs) resultSV lhs (typ, var)
  = ( vcat $ loweringSetup selected
          ++ [assignment]
          ++ loweringCleanup selected
    , loweringRequirements selected
    )
  where doNotAssign (IEEEFP FP_Reinterpret{})
          | not (isFP (kindOf resultSV) || any (isFP . kindOf) opArgs)
          , not (isWideBV (kindOf resultSV) || any (isWideBV . kindOf) opArgs)
          = True   -- generates a memcpy instead; no simple assignment
        doNotAssign _ = False

        renderedArgs = map (showSV cfg consts) opArgs

        selected = fromMaybe legacy $ chooseLowering
          [ arrayExpr cfg op opArgs resultSV renderedArgs
          , tableExpr cfg (showSV cfg consts) op resultSV
          , setExpr cfg op opArgs (kindOf resultSV) renderedArgs
          , textExpr cfg op opArgs (kindOf resultSV) renderedArgs
          , listExpr cfg op opArgs resultSV renderedArgs
          , adtExpr cfg adts op opArgs resultSV renderedArgs
          , tupleExpr cfg op opArgs resultSV renderedArgs
          , gmpExpr cfg op opArgs (kindOf resultSV) renderedArgs
          , arbitraryFPExpr cfg consts op opArgs (kindOf resultSV) renderedArgs
          , nativeFPExpr consts op opArgs (kindOf resultSV) renderedArgs
          , nativeBVExpr op opArgs (kindOf resultSV) renderedArgs
          , nativeBVOverflowExpr op opArgs renderedArgs
          , wideBVExpr op opArgs (kindOf resultSV) renderedArgs
          ]

        legacy = expressionLowering CByValue [] (p op renderedArgs)

        rhs = loweringExpression selected

        assignment
          | doNotAssign op = typ <+> var P.<> semi <+> rhs P.<> semi
          | True           = lhs <+> text "=" <+> rhs P.<> semi

        rtc = cgRTC cfg

        functionName symbol = fromMaybe (T.unpack symbol) (lookup symbol functionNames)

        functionArguments symbol arguments
          | isJust (lookup symbol functionNames) = text "&__sbv_function_ctx" : arguments
          | True                                 = arguments

        cBinOps = [ (Plus, "+"),  (Times, "*"), (Minus, "-")
                  , (Equal False, "==")  -- no strong equality!
                  , (NotEqual, "!="), (LessThan, "<"), (GreaterThan, ">"), (LessEq, "<="), (GreaterEq, ">=")
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
        p ReadArray{}       _  = tbd "User specified arrays (ReadArray)"
        p WriteArray{}      _  = tbd "User specified arrays (WriteArray)"
        p (Label s)        [a] = a <+> text "/*" <+> text s <+> text "*/"
        p (IEEEFP w)         as = handleIEEE w  consts (zip opArgs as) var
        p (PseudoBoolean pb) as = handlePB pb as
        p OverflowOp{}      _   = die "Overflow operation escaped the exact bit-vector lowering pipeline"
        p (KindCast _ to)   [a] = parens (text (show to)) <+> a
        p (Uninterpreted s) []
          | isJust (lookup s functionNames)
          = text "/* Defined function */" <+> text (functionName s) P.<> parens (text "&__sbv_function_ctx")
          | True
          = text "/* Uninterpreted constant */" <+> text (functionName s)
        p (Uninterpreted s) as = text "/* Uninterpreted function */" <+> text (functionName s)
                                  P.<> parens (fsep (punctuate comma (functionArguments s as)))
        p Extract{} _          = die "Bit-vector extraction escaped the exact bit-vector lowering pipeline"
        p Join      _          = die "Bit-vector concatenation escaped the exact bit-vector lowering pipeline"
        p Rol{} _              = die "Left rotation escaped the exact bit-vector lowering pipeline"
        p Ror{} _              = die "Right rotation escaped the exact bit-vector lowering pipeline"
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

                lkUp = text "table" P.<> int t P.<> brackets renderedIndex
                cndLkUp cnd = cnd <+> text "?" <+> defVal <+> text ":" <+> lkUp

                checkLeft
                  | isWideBV k = text "!" P.<> parens (wideBVLookupInRange k len index)
                  | True       = index <+> text "< 0"

                checkRight
                  | isWideBV k = text "!" P.<> parens (wideBVLookupInRange k len index)
                  | True       = index <+> text ">=" <+> int len

                checkBoth  = parens (checkLeft <+> text "||" <+> checkRight)

                renderedIndex
                  | isWideBV k = wideBVLookupIndex k index
                  | True       = index

                canOverflow True  sz = (2::Integer)^(sz-1)-1 >= fromIntegral len
                canOverflow False sz = (2::Integer)^sz    -1 >= fromIntegral len

                (needsCheckL, needsCheckR) = case k of
                                               KVar{}          -> die $ "array index with variable: " ++ show k
                                               KBool           -> (False, canOverflow False (1::Int))
                                               KBounded sg sz
                                                 | isWideBV k -> (sg, not sg)
                                                 | True       -> (sg, canOverflow sg sz)
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
                                               KList     s     -> die $ "List sort "   ++ show s
                                               KSet      s     -> die $ "Set sort "    ++ show s
                                               KTuple    s     -> die $ "Tuple sort "  ++ show s
                                               KArray    k1 k2 -> die $ "Array  sort " ++ show (k1, k2)
                                               KApp      s _   -> die $ "ADT app: " ++ s
                                               KADT      s _ _ -> die $ "ADT: "     ++ s

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
        headerMeta  = [ss | (_, (CgHeader ss, _)) <- files]
        typeDecls   = nubBy sameDoc [t | t:_ <- headerMeta]
        sigs        = concat [ss | _:ss <- headerMeta]
        anyMake     = not (null [() | (_, (CgMakefile{}, _)) <- files])
        drivers     = [ds | (_, (CgDriver, ds)) <- files]
        anyDriver   = not (null drivers)
        mkFlags     = nub (concat [xs | (_, (CgMakefile xs, _)) <- files])
        sources     = [(f, (CgSource, [pre, libHInclude, post])) | (f, (CgSource, [pre, _, post])) <- files]
        sourceNms   = map fst sources
        libHeader   = (libName ++ ".h", (CgHeader (vcat typeDecls : sigs), [genHeader bundleKind libName sigs empty (vcat typeDecls)]))
        libHInclude =  text "#include" <+> text (show (libName ++ ".h"))
                    $$ if "-lbf" `elem` mkFlags then text "#include <libbf.h>" else empty
        libMake     = ("Makefile", (CgMakefile mkFlags, [genLibMake anyDriver libName sourceNms mkFlags]))
        libDriver   = (libName ++ "_driver.c", (CgDriver, mergeDrivers libName libHInclude (zip (map takeBaseName sourceNms) drivers)))
        finalCfg    = case cfgBundles of
                        []         -> defaultCgConfig
                        ((c, _):_) -> c

        sameDoc left right = render left == render right

-- | Create a Makefile for the library
genLibMake :: Bool -> String -> [String] -> [String] -> Doc
genLibMake ifdr libName fs ldFlags = foldr1 ($$) [l | (True, l) <- lns]
 where ifld = not (null ldFlags)
       gmp  = "-lgmp" `elem` ldFlags
       ld | ifld = text "${LDFLAGS}"
          | True = empty
       renderedLDFlags = unwords $ filter (/= "-lgmp") ldFlags ++ ["${GMP_LIBS}" | gmp]
       gmpCFlags
         | gmp       = " ${GMP_CFLAGS}"
         | True      = ""
       lns = [ (True, text "# Makefile for" <+> nm P.<> text ". Automatically generated by SBV. Do not edit!")
             , (True,  text "")
             , (True,  text "# include any user-defined .mk file in the current directory.")
             , (True,  text "-include *.mk")
             , (True,  text "")
             , (True,  text "CC?=gcc")
             , (True,  text "CCFLAGS?=-Wall -O3 -DNDEBUG -fomit-frame-pointer")
             , (gmp,   text "GMP_CFLAGS?=$(shell pkg-config --cflags gmp)")
             , (gmp,   text "GMP_LIBS?=$(shell pkg-config --libs gmp)")
             , (ifld,  text "LDFLAGS?=" P.<> text renderedLDFlags)
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
             , (ifdr,  text ("\t${CC} ${CCFLAGS}" ++ gmpCFlags ++ " $< -o $@ " ++ liba) <+> ld)
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
                 $$ text ("\t${CC} ${CCFLAGS}" ++ gmpCFlags ++ " -c $< -o $@")
                 $$ text ""

-- | Create a driver for a library
mergeDrivers :: String -> Doc -> [(FilePath, [Doc])] -> [Doc]
mergeDrivers libName inc ds = pre : concatMap mkDFun ds ++ [callDrivers (map fst ds)]
  where pre =  text "/* Example driver program for" <+> text libName P.<> text ". */"
            $$ text "/* Automatically generated by SBV. Edit as you see fit! */"
            $$ text ""
            $$ text "#include <stdio.h>"
            $$ inc
        mkDFun (f, [_pre, _include, callbacks, helpers, _header, body, _post]) = [callbacks, helpers, header, body, post]
           where header =  text ""
                        $$ text ("void " ++ f ++ "_driver(void)")
                        $$ text "{"
                 post   =  text "}"
        mkDFun (f, [_pre, _include, helpers, _header, body, _post]) = [helpers, header, body, post]
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

-- | Return the runtime requirements introduced by a legacy scalar operation.
operationRequirements :: CgConfig -> (Op, Kind) -> Set.Set CRequirement
operationRequirements cfg (o, k) = Set.fromList (required o)
  where required (IEEEFP FP_Cast{}) = math
        required (IEEEFP fop)
          | fop `elem` requiresMath = math
        required Abs
          | usesNativeFloatingPoint k = math
        required _ = []

        math = [CRequiresLibM]

        usesNativeFloatingPoint KFloat = True
        usesNativeFloatingPoint KDouble = True
        usesNativeFloatingPoint KReal   = not (isExactGMPKind cfg KReal)
        usesNativeFloatingPoint _       = False

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

-- | Translate collected runtime requirements to external C linker options.
requirementLDFlags :: Set.Set CRequirement -> [String]
requirementLDFlags requirements =
  [ flag
  | (requirement, flag) <- [ (CRequiresGMP, "-lgmp")
                           , (CRequiresLibBF, "-lbf")
                           , (CRequiresLibM, "-lm")
                           ]
  , requirement `Set.member` requirements
  ]

{- HLint ignore module "Redundant lambda" -}
