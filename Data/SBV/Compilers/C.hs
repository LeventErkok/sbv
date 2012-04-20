-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Compilers.C
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Compilation of symbolic programs to C
-----------------------------------------------------------------------------

{-# LANGUAGE PatternGuards #-}

module Data.SBV.Compilers.C(compileToC, compileToCLib, compileToC', compileToCLib') where

import Control.DeepSeq               (rnf)
import Data.Char                     (isSpace)
import Data.List                     (nub)
import Data.Maybe                    (isJust, fromMaybe, isNothing)
import qualified Data.Foldable as F  (toList)
import System.FilePath               (takeBaseName, replaceExtension)
import System.Random
import Text.PrettyPrint.HughesPJ

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum (shex)
import Data.SBV.Compilers.CodeGen

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
-- Compilation will also generate a @Makefile@,  a header file, and a driver (test) program, etc.
compileToC :: Maybe FilePath -> String -> SBVCodeGen () -> IO ()
compileToC mbDirName nm f = compileToC' nm f >>= renderCgPgmBundle mbDirName

-- | Lower level version of 'compileToC', producing a 'CgPgmBundle'
compileToC' :: String -> SBVCodeGen () -> IO CgPgmBundle
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
compileToCLib :: Maybe FilePath -> String -> [(String, SBVCodeGen ())] -> IO ()
compileToCLib mbDirName libName comps = compileToCLib' libName comps >>= renderCgPgmBundle mbDirName

-- | Lower level version of 'compileToCLib', producing a 'CgPgmBundle'
compileToCLib' :: String -> [(String, SBVCodeGen ())] -> IO CgPgmBundle
compileToCLib' libName comps = mergeToLib libName `fmap` mapM (uncurry compileToC') comps

---------------------------------------------------------------------------
-- * Implementation
---------------------------------------------------------------------------

-- token for the target language
data SBVToC = SBVToC

instance CgTarget SBVToC where
  targetName _ = "C"
  translate _  = cgen

-- Unexpected input, or things we will probably never support
die :: String -> a
die msg = error $ "SBV->C: Unexpected: " ++ msg

-- Unbounded int
dieUnbounded :: a
dieUnbounded = error $    "SBV->C: Unbounded integers are not supported by the C compiler."
                     ++ "\nUse 'cgIntegerSize' to specify a fixed size for SInteger representation."

-- Reals
dieReal :: a
dieReal = error "SBV->C: SReal values are not supported by the C compiler."

-- Unsupported features, or features TBD
tbd :: String -> a
tbd msg = error $ "SBV->C: Not yet supported: " ++ msg

cgen :: CgConfig -> String -> CgState -> Result -> CgPgmBundle
cgen cfg nm st sbvProg
   -- we rnf the sig to make sure any exceptions in type conversion pop-out early enough
   -- this is purely cosmetic, of course..
   = rnf (render sig) `seq` result
  where result = CgPgmBundle $ filt [ ("Makefile",  (CgMakefile flags, [genMake (cgGenDriver cfg) nm nmd flags]))
                                    , (nm  ++ ".h", (CgHeader [sig],   [genHeader nm [sig] extProtos]))
                                    , (nmd ++ ".c", (CgDriver,         genDriver mbISize randVals nm ins outs mbRet))
                                    , (nm  ++ ".c", (CgSource,         genCProg rtc mbISize nm sig sbvProg ins outs mbRet extDecls))
                                    ]
        rtc      = cgRTC cfg
        mbISize  = cgInteger cfg
        randVals = cgDriverVals cfg
        filt xs  = [c | c@(_, (k, _)) <- xs, need k]
          where need k | isCgDriver   k = cgGenDriver cfg
                       | isCgMakefile k = cgGenMakefile cfg
                       | True           = True
        nmd      = nm ++ "_driver"
        sig      = pprCFunHeader mbISize nm ins outs mbRet
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
                     xs -> vcat $ text "/* User given declarations: */" : map text xs ++ [text ""]
        flags    = cgLDFlags st

cSizeOf :: Maybe Int -> HasKind a => a -> Int
cSizeOf mbIntSize x
  | isReal x    = dieReal
  | isInteger x = fromMaybe dieUnbounded mbIntSize
  | True        = intSizeOf x

-- | Pretty print a functions type. If there is only one output, we compile it
-- as a function that returns that value. Otherwise, we compile it as a void function
-- that takes return values as pointers to be updated.
pprCFunHeader :: Maybe Int -> String -> [(String, CgVal)] -> [(String, CgVal)] -> Maybe SW -> Doc
pprCFunHeader mbISize fn ins outs mbRet = retType <+> text fn <> parens (fsep (punctuate comma (map (mkParam mbISize) ins ++ map (mkPParam mbISize) outs)))
  where retType = case mbRet of
                   Nothing -> text "void"
                   Just sw -> pprCWord False (hasSign sw, cSizeOf mbISize sw)

mkParam, mkPParam :: Maybe Int -> (String, CgVal) -> Doc
mkParam  mbISize (n, CgAtomic sw)     = let sgsz = (hasSign sw, cSizeOf mbISize sw) in pprCWord True  sgsz <+> text n
mkParam  _       (_, CgArray  [])     = die "mkParam: CgArray with no elements!"
mkParam  mbISize (n, CgArray  (sw:_)) = let sgsz = (hasSign sw, cSizeOf mbISize sw) in pprCWord True  sgsz <+> text "*" <> text n
mkPParam mbISize (n, CgAtomic sw)     = let sgsz = (hasSign sw, cSizeOf mbISize sw) in pprCWord False sgsz <+> text "*" <> text n
mkPParam _       (_, CgArray  [])     = die "mPkParam: CgArray with no elements!"
mkPParam mbISize (n, CgArray  (sw:_)) = let sgsz = (hasSign sw, cSizeOf mbISize sw) in pprCWord False sgsz <+> text "*" <> text n

-- | Renders as "const SWord8 s0", etc. the first parameter is the width of the typefield
declSW :: Maybe Int -> Int -> SW -> Doc
declSW mbISize w sw = text "const" <+> pad (showCType (hasSign sw, cSizeOf mbISize sw)) <+> text (show sw)
  where pad s = text $ s ++ replicate (w - length s) ' '

-- | Renders as "s0", etc, or the corresponding constant
showSW :: Maybe Int -> [(SW, CW)] -> SW -> Doc
showSW mbISize consts sw
  | sw == falseSW                 = text "false"
  | sw == trueSW                  = text "true"
  | Just cw <- sw `lookup` consts = showConst mbISize cw
  | True                          = text $ show sw

-- | Words as it would map to a C word
pprCWord :: Bool -> (Bool, Int) -> Doc
pprCWord cnst sgsz = (if cnst then text "const" else empty) <+> text (showCType sgsz)

showCType :: (Bool, Int) -> String
showCType (False, 1) = "SBool"
showCType (s, sz)
  | sz `elem` [8, 16, 32, 64] = t
  | True                      = die $ "Non-regular bitvector type: " ++ t
 where t = (if s then "SInt" else "SWord") ++ show sz

-- | The printf specifier for the type
specifier :: (Bool, Int) -> Doc
specifier (False,  1) = text "%d"
specifier (False,  8) = text "%\"PRIu8\""
specifier (True,   8) = text "%\"PRId8\""
specifier (False, 16) = text "0x%04\"PRIx16\"U"
specifier (True,  16) = text "%\"PRId16\""
specifier (False, 32) = text "0x%08\"PRIx32\"UL"
specifier (True,  32) = text "%\"PRId32\"L"
specifier (False, 64) = text "0x%016\"PRIx64\"ULL"
specifier (True,  64) = text "%\"PRId64\"LL"
specifier (s, sz)     = die $ "Format specifier at type " ++ (if s then "SInt" else "SWord") ++ show sz

-- | Make a constant value of the given type. We don't check for out of bounds here, as it should not be needed.
--   There are many options here, using binary, decimal, etc. We simply
--   8-bit or less constants using decimal; otherwise we use hex.
--   Note that this automatically takes care of the boolean (1-bit) value problem, since it
--   shows the result as an integer, which is OK as far as C is concerned.
mkConst :: Integer -> (Bool, Int) -> Doc
mkConst i   (False,  1) = text (if i == 0 then "false" else "true")
mkConst i   (False,  8) = integer i
mkConst i   (True,   8) = integer i
mkConst i t@(False, 16) = text (shex False True t i) <> text "U"
mkConst i t@(True,  16) = text (shex False True t i)
mkConst i t@(False, 32) = text (shex False True t i) <> text "UL"
mkConst i t@(True,  32) = text (shex False True t i) <> text "L"
mkConst i t@(False, 64) = text (shex False True t i) <> text "ULL"
mkConst i t@(True,  64) = text (shex False True t i) <> text "LL"
mkConst i   (True,  1)  = die $ "Signed 1-bit value " ++ show i
mkConst i   (s, sz)     = die $ "Constant " ++ show i ++ " at type " ++ (if s then "SInt" else "SWord") ++ show sz

-- | Show a constant
showConst :: Maybe Int -> CW -> Doc
showConst mbISize  cw@(CW _ (Right v)) = mkConst v (hasSign cw, cSizeOf mbISize cw)
showConst _mbISize cw                  = die $ "showConst: " ++ show cw

-- | Generate a makefile. The first argument is True if we have a driver.
genMake :: Bool -> String -> String -> [String] -> Doc
genMake ifdr fn dn ldFlags = foldr1 ($$) [l | (True, l) <- lns]
 where ifld = not (null ldFlags)
       ld | ifld = text "${LDFLAGS}"
          | True = empty
       lns = [ (True, text "# Makefile for" <+> nm <> text ". Automatically generated by SBV. Do not edit!")
             , (True, text "")
             , (True, text "# include any user-defined .mk file in the current directory.")
             , (True, text "-include *.mk")
             , (True, text "")
             , (True, text "CC=gcc")
             , (True, text "CCFLAGS?=-Wall -O3 -DNDEBUG -fomit-frame-pointer")
             , (ifld, text "LDFLAGS?=" <> text (unwords ldFlags))
             , (True, text "")
             , (ifdr, text "all:" <+> nmd)
             , (ifdr, text "")
             , (True, nmo <> text (": " ++ ppSameLine (hsep [nmc, nmh])))
             , (True, text "\t${CC} ${CCFLAGS}" <+> text "-c $< -o $@")
             , (True, text "")
             , (ifdr, nmdo <> text ":" <+> nmdc)
             , (ifdr, text "\t${CC} ${CCFLAGS}" <+> text "-c $< -o $@")
             , (ifdr, text "")
             , (ifdr, nmd <> text (": " ++ ppSameLine (hsep [nmo, nmdo])))
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
       nmh  = nm <> text ".h"
       nmc  = nm <> text ".c"
       nmo  = nm <> text ".o"
       nmdc = nmd <> text ".c"
       nmdo = nmd <> text ".o"

-- | Generate the header
genHeader :: String -> [Doc] -> Doc -> Doc
genHeader fn sigs protos =
     text "/* Header file for" <+> nm <> text ". Automatically generated by SBV. Do not edit! */"
  $$ text ""
  $$ text "#ifndef" <+> tag
  $$ text "#define" <+> tag
  $$ text ""
  $$ text "#include <inttypes.h>"
  $$ text "#include <stdint.h>"
  $$ text "#include <stdbool.h>"
  $$ text ""
  $$ text "/* The boolean type */"
  $$ text "typedef bool SBool;"
  $$ text ""
  $$ text "/* Unsigned bit-vectors */"
  $$ text "typedef uint8_t  SWord8 ;"
  $$ text "typedef uint16_t SWord16;"
  $$ text "typedef uint32_t SWord32;"
  $$ text "typedef uint64_t SWord64;"
  $$ text ""
  $$ text "/* Signed bit-vectors */"
  $$ text "typedef int8_t  SInt8 ;"
  $$ text "typedef int16_t SInt16;"
  $$ text "typedef int32_t SInt32;"
  $$ text "typedef int64_t SInt64;"
  $$ text ""
  $$ text ("/* Entry point prototype" ++ plu ++ ": */")
  $$ vcat (map (<> semi) sigs)
  $$ text ""
  $$ protos
  $$ text "#endif /*" <+> tag <+> text "*/"
  $$ text ""
 where nm  = text fn
       tag = text "__" <> nm <> text "__HEADER_INCLUDED__"
       plu = if length sigs /= 1 then "s" else ""

sepIf :: Bool -> Doc
sepIf b = if b then text "" else empty

-- | Generate an example driver program
genDriver :: Maybe Int -> [Integer] -> String -> [(String, CgVal)] -> [(String, CgVal)] -> Maybe SW -> [Doc]
genDriver mbISize randVals fn inps outs mbRet = [pre, header, body, post]
 where pre    =  text "/* Example driver program for" <+> nm <> text ". */"
              $$ text "/* Automatically generated by SBV. Edit as you see fit! */"
              $$ text ""
              $$ text "#include <inttypes.h>"
              $$ text "#include <stdint.h>"
              $$ text "#include <stdbool.h>"
              $$ text "#include <stdio.h>"
       header =  text "#include" <+> doubleQuotes (nm <> text ".h")
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
                              Just sw -> text "printf" <> parens (printQuotes (fcall <+> text "=" <+> specifier (hasSign sw, cSizeOf mbISize sw) <> text "\\n")
                                                                              <> comma <+> resultVar) <> semi
                              Nothing -> text "printf" <> parens (printQuotes (fcall <+> text "->\\n")) <> semi)
                      $$ vcat (map display outs)
                      )
       post   =   text ""
              $+$ nest 2 (text "return 0" <> semi)
              $$  text "}"
              $$  text ""
       nm = text fn
       pairedInputs = matchRands (map abs randVals) inps
       matchRands _      []                                 = []
       matchRands []     _                                  = die "Run out of driver values!"
       matchRands (r:rs) ((n, CgAtomic sw)            : cs) = ([mkRVal sw r], n, CgAtomic sw) : matchRands rs cs
       matchRands _      ((n, CgArray [])             : _ ) = die $ "Unsupported empty array input " ++ show n
       matchRands rs     ((n, a@(CgArray sws@(sw:_))) : cs)
          | length frs /= l                                 = die "Run out of driver values!"
          | True                                            = (map (mkRVal sw) frs, n, a) : matchRands srs cs
          where l          = length sws
                (frs, srs) = splitAt l rs
       mkRVal sw r = mkConst ival sgsz
         where sgsz@(sg, sz) = (hasSign sw, cSizeOf mbISize sw)
               ival | r >= minVal && r <= maxVal = r
                    | not sg                     = r `mod` (2^sz)
                    | True                       = (r `mod` (2^sz)) - (2^(sz-1))
                    where expSz, expSz', minVal, maxVal :: Integer
                          expSz  = 2^(sz-1)
                          expSz' = 2*expSz
                          minVal | not sg = 0
                                 | True   = -expSz
                          maxVal | not sg = expSz'-1
                                 | True   = expSz-1
       mkInp (_,  _, CgAtomic{})         = empty  -- constant, no need to declare
       mkInp (_,  n, CgArray [])         = die $ "Unsupported empty array value for " ++ show n
       mkInp (vs, n, CgArray sws@(sw:_)) =  pprCWord True (hasSign sw, cSizeOf mbISize sw) <+> text n <> brackets (int (length sws)) <+> text "= {"
                                                      $$ nest 4 (fsep (punctuate comma (align vs)))
                                                      $$ text "};"
                                         $$ text ""
                                         $$ text "printf" <> parens (printQuotes (text "Contents of input array" <+> text n <> text ":\\n")) <> semi
                                         $$ display (n, CgArray sws)
                                         $$ text ""
       mkOut (v, CgAtomic sw)            = let sgsz = (hasSign sw, cSizeOf mbISize sw) in pprCWord False sgsz <+> text v <> semi
       mkOut (v, CgArray [])             = die $ "Unsupported empty array value for " ++ show v
       mkOut (v, CgArray sws@(sw:_))     = pprCWord False (hasSign sw, cSizeOf mbISize sw) <+> text v <> brackets (int (length sws)) <> semi
       resultVar = text "__result"
       call = case mbRet of
                Nothing -> fcall <> semi
                Just sw -> pprCWord True (hasSign sw, cSizeOf mbISize sw) <+> resultVar <+> text "=" <+> fcall <> semi
       fcall = nm <> parens (fsep (punctuate comma (map mkCVal pairedInputs ++ map mkOVal outs)))
       mkCVal ([v], _, CgAtomic{}) = v
       mkCVal (vs,  n, CgAtomic{}) = die $ "Unexpected driver value computed for " ++ show n ++ render (hcat vs)
       mkCVal (_,   n, CgArray{})  = text n
       mkOVal (n, CgAtomic{})      = text "&" <> text n
       mkOVal (n, CgArray{})       = text n
       display (n, CgAtomic sw)         = text "printf" <> parens (printQuotes (text " " <+> text n <+> text "=" <+> specifier (hasSign sw, cSizeOf mbISize sw)
                                                                                <> text "\\n") <> comma <+> text n) <> semi
       display (n, CgArray [])         =  die $ "Unsupported empty array value for " ++ show n
       display (n, CgArray sws@(sw:_)) =   text "int" <+> nctr <> semi
                                        $$ text "for(" <> nctr <+> text "= 0;" <+> nctr <+> text "<" <+> int (length sws) <+> text "; ++" <> nctr <> text ")"
                                        $$ nest 2 (text "printf" <> parens (printQuotes (text " " <+> entrySpec <+> text "=" <+> spec <> text "\\n")
                                                                 <> comma <+> nctr <+> comma <> entry) <> semi)
                  where nctr      = text n <> text "_ctr"
                        entry     = text n <> text "[" <> nctr <> text "]"
                        entrySpec = text n <> text "[%d]"
                        spec      = specifier (hasSign sw, cSizeOf mbISize sw)

-- | Generate the C program
genCProg :: Bool -> Maybe Int -> String -> Doc -> Result -> [(String, CgVal)] -> [(String, CgVal)] -> Maybe SW -> Doc -> [Doc]
genCProg rtc mbISize fn proto (Result hasInfPrec _ cgs ins preConsts tbls arrs _ _ asgns cstrs _) inVars outVars mbRet extDecls
  | isNothing mbISize && hasInfPrec = dieUnbounded
  | not (null cstrs)                = tbd "Explicit constraints"
  | not (null arrs)                 = tbd "User specified arrays"
  | needsExistentials (map fst ins) = error "SBV->C: Cannot compile functions with existentially quantified variables."
  | True                            = [pre, header, post]
 where pre    = text "/* File:" <+> doubleQuotes (nm <> text ".c") <> text ". Automatically generated by SBV. Do not edit! */"
              $$ text ""
              $$ text "#include <inttypes.h>"
              $$ text "#include <stdint.h>"
              $$ text "#include <stdbool.h>"
       header = text "#include" <+> doubleQuotes (nm <> text ".h")
       post   = text ""
             $$ vcat (map codeSeg cgs)
             $$ extDecls
             $$ proto
             $$ text "{"
             $$ text ""
             $$ nest 2 (   vcat (concatMap (genIO True) inVars)
                        $$ vcat (merge (map genTbl tbls) (map genAsgn assignments))
                        $$ sepIf (not (null assignments) || not (null tbls))
                        $$ vcat (concatMap (genIO False) outVars)
                        $$ maybe empty mkRet mbRet
                       )
             $$ text "}"
             $$ text ""
       nm = text fn
       assignments = F.toList asgns
       codeSeg (fnm, ls) =  text "/* User specified custom code for" <+> doubleQuotes (text fnm) <+> text "*/"
                         $$ vcat (map text ls)
                         $$ text ""
       typeWidth = getMax 0 [len (hasSign s, cSizeOf mbISize s) | (s, _) <- assignments]
                where len (False, 1) = 5 -- SBool
                      len (False, n) = 5 + length (show n) -- SWordN
                      len (True,  n) = 4 + length (show n) -- SIntN
                      getMax 7 _      = 7  -- 7 is the max we can get with SWord64, so don't bother looking any further
                      getMax m []     = m
                      getMax m (x:xs) = getMax (m `max` x) xs
       consts = (falseSW, falseCW) : (trueSW, trueCW) : preConsts
       isConst s = isJust (lookup s consts)
       genIO :: Bool -> (String, CgVal) -> [Doc]
       genIO True  (cNm, CgAtomic sw) = [declSW mbISize typeWidth sw  <+> text "=" <+> text cNm <> semi]
       genIO False (cNm, CgAtomic sw) = [text "*" <> text cNm <+> text "=" <+> showSW mbISize consts sw <> semi]
       genIO isInp (cNm, CgArray sws) = zipWith genElt sws [(0::Int)..]
         where genElt sw i
                 | isInp = declSW mbISize typeWidth sw <+> text "=" <+> text entry       <> semi
                 | True  = text entry                  <+> text "=" <+> showSW mbISize consts sw <> semi
                 where entry = cNm ++ "[" ++ show i ++ "]"
       mkRet sw = text "return" <+> showSW mbISize consts sw <> semi
       genTbl :: ((Int, Kind, Kind), [SW]) -> (Int, Doc)
       genTbl ((i, _, k), elts) =  (location, static <+> pprCWord True (sg, szv) <+> text ("table" ++ show i) <> text "[] = {"
                                              $$ nest 4 (fsep (punctuate comma (align (map (showSW mbISize consts) elts))))
                                              $$ text "};")
         where (sg, szv) = case (mbISize, k) of
                            (_,       KBounded b v) -> (b, v)
                            (Just is, KUnbounded)   -> (True, is)
                            (Nothing, KUnbounded)   -> dieUnbounded
                            (_,       KReal)        -> dieReal
               static   = if location == -1 then text "static" else empty
               location = maximum (-1 : map getNodeId elts)
       getNodeId s@(SW _ (NodeId n)) | isConst s = -1
                                     | True      = n
       genAsgn :: (SW, SBVExpr) -> (Int, Doc)
       genAsgn (sw, n) = (getNodeId sw, declSW mbISize typeWidth sw <+> text "=" <+> ppExpr mbISize rtc consts n <> semi)
       -- merge tables intermixed with assignments, paying attention to putting tables as
       -- early as possible.. Note that the assignment list (second argument) is sorted on its order
       merge :: [(Int, Doc)] -> [(Int, Doc)] -> [Doc]
       merge []               as                  = map snd as
       merge ts               []                  = map snd ts
       merge ts@((i, t):trest) as@((i', a):arest)
         | i < i'                                 = t : merge trest as
         | True                                   = a : merge ts arest

ppExpr :: Maybe Int -> Bool -> [(SW, CW)] -> SBVExpr -> Doc
ppExpr mbISize rtc consts (SBVApp op opArgs) = p op (map (showSW mbISize consts) opArgs)
  where cBinOps = [ (Plus, "+"), (Times, "*"), (Minus, "-")
                  , (Equal, "=="), (NotEqual, "!=")
                  , (LessThan, "<"), (GreaterThan, ">"), (LessEq, "<="), (GreaterEq, ">=")
                  , (And, "&"), (Or, "|"), (XOr, "^")
                  ]
        p (ArrRead _)       _  = tbd "User specified arrays (ArrRead)"
        p (ArrEq _ _)       _  = tbd "User specified arrays (ArrEq)"
        p (Uninterpreted s) [] = text "/* Uninterpreted constant */" <+> text s
        p (Uninterpreted s) as = text "/* Uninterpreted function */" <+> text s <> parens (fsep (punctuate comma as))
        p (Extract i j) [a]    = extract i j (let s = head opArgs in (hasSign s, cSizeOf mbISize s)) a
        p Join [a, b]          = join (let (s1 : s2 : _) = opArgs in ((hasSign s1, cSizeOf mbISize s1), (hasSign s2, cSizeOf mbISize s2), a, b))
        p (Rol i) [a]          = rotate True  i a (let s = head opArgs in (hasSign s, cSizeOf mbISize s))
        p (Ror i) [a]          = rotate False i a (let s = head opArgs in (hasSign s, cSizeOf mbISize s))
        p (Shl i) [a]          = shift True  i a (let s = head opArgs in (hasSign s, cSizeOf mbISize s))
        p (Shr i) [a]          = shift False i a (let s = head opArgs in (hasSign s, cSizeOf mbISize s))
        p Not [a]
          -- be careful about booleans, bitwise complement is not correct for them!
          | s == 1
          = text "!" <> a
          | True
          = text "~" <> a
          where s = cSizeOf mbISize (head opArgs)
        p Ite [a, b, c] = a <+> text "?" <+> b <+> text ":" <+> c
        p (LkUp (t, k, _, len) ind def) []
          | not rtc                    = lkUp -- ignore run-time-checks per user request
          | needsCheckL && needsCheckR = cndLkUp checkBoth
          | needsCheckL                = cndLkUp checkLeft
          | needsCheckR                = cndLkUp checkRight
          | True                       = lkUp
          where (as, at) = case (mbISize, k) of
                            (_,       KBounded b v) -> (b, v)
                            (Just i,  KUnbounded)   -> (True, i)
                            (Nothing, KUnbounded)   -> dieUnbounded
                            (_,       KReal)        -> dieReal
                [index, defVal] = map (showSW mbISize consts) [ind, def]
                lkUp = text "table" <> int t <> brackets (showSW mbISize consts ind)
                cndLkUp cnd = cnd <+> text "?" <+> defVal <+> text ":" <+> lkUp
                checkLeft  = index <+> text "< 0"
                checkRight = index <+> text ">=" <+> int len
                checkBoth  = parens (checkLeft <+> text "||" <+> checkRight)
                (needsCheckL, needsCheckR) | as   = (True,  (2::Integer)^(at-1)-1  >= fromIntegral len)
                                           | True = (False, (2::Integer)^at    -1  >= fromIntegral len)
        -- Div/Rem should be careful on 0, in the SBV world x `div` 0 is 0, x `rem` 0 is x
        p Quot [a, b] = parens (b <+> text "== 0") <+> text "?" <+> text "0" <+> text ":" <+> parens (a <+> text "/" <+> b)
        p Rem  [a, b] = parens (b <+> text "== 0") <+> text "?" <+>    a     <+> text ":" <+> parens (a <+> text "%" <+> b)
        p o [a, b]
          | Just co <- lookup o cBinOps
          = a <+> text co <+> b
        p o args = die $ "Received operator " ++ show o ++ " applied to " ++ show args
        shift toLeft i a (sg, sz)
          | i < 0   = shift (not toLeft) (-i) a (sg, sz)
          | i == 0  = a
          | i >= sz = mkConst 0 (sg, sz)
          | True    = a <+> text cop <+> int i
          where cop | toLeft = "<<"
                    | True   = ">>"
        rotate toLeft i a (True, sz)
          = tbd $ "Rotation of signed words at size " ++ show (toLeft, i, a, sz)
        rotate toLeft i a (False, sz)
          | i < 0   = rotate (not toLeft) (-i) a (False, sz)
          | i == 0  = a
          | i >= sz = rotate toLeft (i `mod` sz) a (False, sz)
          | True    =     parens (a <+> text cop  <+> int i)
                      <+> text "|"
                      <+> parens (a <+> text cop' <+> int (sz - i))
          where (cop, cop') | toLeft = ("<<", ">>")
                            | True   = (">>", "<<")
        -- TBD: below we only support the values that SBV actually currently generates.
        -- we would need to add new ones if we generate others. (Check instances in Data/SBV/BitVectors/Splittable.hs).
        extract 63 32 (False, 64) a = text "(SWord32)" <+> parens (a <+> text ">> 32")
        extract 31  0 (False, 64) a = text "(SWord32)" <+> a
        extract 31 16 (False, 32) a = text "(SWord16)" <+> parens (a <+> text ">> 16")
        extract 15  0 (False, 32) a = text "(SWord16)" <+> a
        extract 15  8 (False, 16) a = text "(SWord8)"  <+> parens (a <+> text ">> 8")
        extract  7  0 (False, 16) a = text "(SWord8)"  <+> a
        -- the followings are used by sign-conversions. (Check instances in Data/SBV/BitVectors/SignCast.hs).
        extract 63  0 (False, 64) a = text "(SInt64)"  <+> a
        extract 63  0 (True,  64) a = text "(SWord64)" <+> a
        extract 31  0 (False, 32) a = text "(SInt32)"  <+> a
        extract 31  0 (True,  32) a = text "(SWord32)" <+> a
        extract 15  0 (False, 16) a = text "(SInt16)"  <+> a
        extract 15  0 (True,  16) a = text "(SWord16)" <+> a
        extract  7  0 (False,  8) a = text "(SInt8)"   <+> a
        extract  7  0 (True,   8) a = text "(SWord8)"  <+> a
        extract  i  j (sg, sz)    _ = tbd $ "extract with " ++ show (i, j, (sg, sz))
        -- TBD: ditto here for join, just like extract above
        join ((False,  8), (False,  8), a, b) = parens (parens (text "(SWord16)" <+> a) <+> text "<< 8")  <+> text "|" <+> parens (text "(SWord16)" <+> b)
        join ((False, 16), (False, 16), a, b) = parens (parens (text "(SWord32)" <+> a) <+> text "<< 16") <+> text "|" <+> parens (text "(SWord32)" <+> b)
        join ((False, 32), (False, 32), a, b) = parens (parens (text "(SWord64)" <+> a) <+> text "<< 32") <+> text "|" <+> parens (text "(SWord64)" <+> b)
        join (sgsz1, sgsz2, _, _)             = tbd $ "join with " ++ show (sgsz1, sgsz2)

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

-- | Merge a bunch of bundles to generate code for a library
mergeToLib :: String -> [CgPgmBundle] -> CgPgmBundle
mergeToLib libName bundles = CgPgmBundle $ sources ++ libHeader : [libDriver | anyDriver] ++ [libMake | anyMake]
  where files       = concat [fs | CgPgmBundle fs <- bundles]
        sigs        = concat [ss | (_, (CgHeader ss, _)) <- files]
        anyMake     = not (null [() | (_, (CgMakefile{}, _)) <- files])
        drivers     = [ds | (_, (CgDriver, ds)) <- files]
        anyDriver   = not (null drivers)
        mkFlags     = nub (concat [xs | (_, (CgMakefile xs, _)) <- files])
        sources     = [(f, (CgSource, [pre, libHInclude, post])) | (f, (CgSource, [pre, _, post])) <- files]
        sourceNms   = map fst sources
        libHeader   = (libName ++ ".h", (CgHeader sigs, [genHeader libName sigs empty]))
        libHInclude = text "#include" <+> text (show (libName ++ ".h"))
        libMake     = ("Makefile", (CgMakefile mkFlags, [genLibMake anyDriver libName sourceNms mkFlags]))
        libDriver   = (libName ++ "_driver.c", (CgDriver, mergeDrivers libName libHInclude (zip (map takeBaseName sourceNms) drivers)))

-- | Create a Makefile for the library
genLibMake :: Bool -> String -> [String] -> [String] -> Doc
genLibMake ifdr libName fs ldFlags = foldr1 ($$) [l | (True, l) <- lns]
 where ifld = not (null ldFlags)
       ld | ifld = text "${LDFLAGS}"
          | True = empty
       lns = [ (True, text "# Makefile for" <+> nm <> text ". Automatically generated by SBV. Do not edit!")
             , (True,  text "")
             , (True,  text "# include any user-defined .mk file in the current directory.")
             , (True,  text "-include *.mk")
             , (True,  text "")
             , (True,  text "CC=gcc")
             , (True,  text "CCFLAGS?=-Wall -O3 -DNDEBUG -fomit-frame-pointer")
             , (ifld,  text "LDFLAGS?=" <> text (unwords ldFlags))
             , (True,  text "AR=ar")
             , (True,  text "ARFLAGS=cr")
             , (True,  text "")
             , (not ifdr,  text ("all: " ++ liba))
             , (ifdr,      text ("all: " ++ unwords [liba, libd]))
             , (True,  text "")
             , (True,  text liba <> text (": " ++ unwords os))
             , (True,  text "\t${AR} ${ARFLAGS} $@ $^")
             , (True,  text "")
             , (ifdr,  text libd <> text (": " ++ unwords [libd ++ ".c", libh]))
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
       mkObj o f =  text o <> text (": " ++ unwords [f, libh])
                 $$ text "\t${CC} ${CCFLAGS} -c $< -o $@"
                 $$ text ""

-- | Create a driver for a library
mergeDrivers :: String -> Doc -> [(FilePath, [Doc])] -> [Doc]
mergeDrivers libName inc ds = pre : concatMap mkDFun ds ++ [callDrivers (map fst ds)]
  where pre =  text "/* Example driver program for" <+> text libName <> text ". */"
            $$ text "/* Automatically generated by SBV. Edit as you see fit! */"
            $$ text ""
            $$ text "#include <inttypes.h>"
            $$ text "#include <stdint.h>"
            $$ text "#include <stdbool.h>"
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
