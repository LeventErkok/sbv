----------------------------------------------------------------------------
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

module Data.SBV.Compilers.C(compileToC, compileToC') where

import Data.Maybe(isJust)
import Text.PrettyPrint.HughesPJ
import System.Random

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum(shex)
import Data.SBV.Compilers.CodeGen

-- token for the target language
data SBVToC = SBVToC

instance SBVTarget SBVToC where
  targetName _ = "C"
  translate _  = cgen

-- Unsupported features, or features TBD go thorough here..
tbd :: String -> a
tbd msg = error $ "SBV->C: " ++ msg

-- | Given a symbolic computation, render it as an equivalent
--   C program. The first argument is an optional directory name
--   under which the files will be saved. If `Nothing`, the result
--   will be written to stdout. Use @`Just` \".\"@ for creating files in
--   the current directory. The second argument is name of the function,
--   which also forms the names of the C and header files. The third argument
--   is the names of the arguments to be used and the names of the outputs, if any.
--   Provide as many arguments as you like, SBV will make up ones if you don't pass
--   enough. The final argument is the computation to be compiled. Compilation will
--   also generate a @Makefile@ and a sample driver program, which executes the program over random
--   input values.
compileToC :: SymExecutable f => Maybe FilePath -> String -> [String] -> f -> IO ()
compileToC mbDir fn extraNames f = do rands <- newStdGen >>= return . randoms
                                      codeGen SBVToC rands mbDir fn extraNames f

-- | Same as 'compileToC', except use the specified values (first argument) instead of random values
-- when generating the driver program. This version is useful mainly for generating repeatable test values.
compileToC' :: SymExecutable f => [Integer] -> Maybe FilePath -> String -> [String] -> f -> IO ()
compileToC' dvals = codeGen SBVToC (dvals ++ repeat 0)

cgen :: [Integer] -> String -> [String] -> Result -> [(FilePath, Doc)]
cgen randVals nm extraNames sbvProg@(Result ins _ _ _ _ _ _ outs) =
        [ ("Makefile",  genMake   nm nmd)
        , (nm  ++ ".h", genHeader nm sig)
        , (nmd ++ ".c", genDriver randVals nm typ)
        , (nm  ++ ".c", genCProg  nm sig sbvProg)
        ]
  where nmd = nm ++ "_driver"
        typ = mkCType extraNames ins outs
        sig = pprCFunHeader nm typ

-- | A simple representation of C types for functions
-- sufficient enough to represent SBV generated functions
newtype CType = CType ([(String, (Bool, Int))], [(String, (Bool, Int))])

mkCType :: [String] -> [NamedSymVar] -> [SW] -> CType
mkCType extraNames ins outs = CType (map mkVar ins, map mkVar (zip outs outNames))
  where outNames = extraNames ++ ["out" ++ show i | i <- [length extraNames ..]]
        mkVar (sw, n) = (n, (hasSign sw, sizeOf sw))

-- | Pretty print a functions type. If there is only one output, we compile it
-- as a function that returns that value. Otherwise, we compile it as a void function
-- that takes return values as pointers to be updated.
pprCFunHeader :: String -> CType -> Doc
pprCFunHeader fn (CType (ins, outs)) = retType <+> text fn <> parens (fsep (punctuate comma (map mkParam ins ++ os)))
  where (retType, os) = case outs of
                          [(_, bs)] -> (pprCWord bs, [])
                          _         -> (text "void", map mkPParam outs)

mkParam, mkPParam :: (String, (Bool, Int)) -> Doc
mkParam  (n, bs) = pprCWord bs <+> text n
mkPParam (n, bs) = pprCWord bs <+> text "*" <> text n

-- | Words as it would be defined in the standard header stdint.h
pprCWord :: (Bool, Int) -> Doc
pprCWord (False, 1) = text "SBool"
pprCWord (s, sz)
  | sz `elem` [8, 16, 32, 64]
  = text $ (if s then "SInt" else "SWord") ++ show sz
pprCWord (s, sz)
  = tbd $ "Unsupported bitvector type: " ++ (if s then "SInt" else "SWord") ++ show sz

-- | The printf specifier for the type
specifier :: (Bool, Int) -> Doc
specifier (False,  1) = text "%d"
specifier (False,  8) = text "%\"PRIu8\""
specifier (True,   8) = text "%\"PRId8\""
specifier (False, 16) = text "%\"PRIu16\""
specifier (True,  16) = text "%\"PRId16\""
specifier (False, 32) = text "%\"PRIu32\""
specifier (True,  32) = text "%\"PRId32\""
specifier (False, 64) = text "%\"PRIu64\""
specifier (True,  64) = text "%\"PRId64\""
specifier (s, sz)     = tbd $ "Unsupported specifier at type " ++ (if s then "SInt" else "SWord") ++ show sz

-- | Make a constant value of the given type. We don't check for out of bounds here, as it should not be needed.
mkConst :: Integer -> (Bool, Int) -> Doc
mkConst i   (False,  1) = integer i
mkConst i t@(False,  8) = text (shex False t i) <> text "U"
mkConst i t@(True,   8) = text (shex False t i)
mkConst i t@(False, 16) = text (shex False t i) <> text "U"
mkConst i t@(True,  16) = text (shex False t i)
mkConst i t@(False, 32) = text (shex False t i) <> text "UL"
mkConst i t@(True,  32) = text (shex False t i) <> text "L"
mkConst i t@(False, 64) = text (shex False t i) <> text "ULL"
mkConst i t@(True,  64) = text (shex False t i) <> text "LL"
mkConst i (s, sz)     = tbd $ "Unsupported constant " ++ show i ++ " at type " ++ (if s then "SInt" else "SWord") ++ show sz

-- | Show a constant. There are many options here, using binary, decimal, etc. We simply
--   8-bit or less constants using decimal; otherwise we use hex.
--   Note that this automatically takes care of the boolean (1-bit) value problem, since it
--   shows the result as an integer, which is OK as far as C is concerned.
showConst :: CW -> Doc
showConst cw
  | sz <= 8 = integer (cwVal cw)
  | True    = text $ shex False sgsz (cwVal cw)
  where sgsz@(_, sz) = (hasSign cw, sizeOf cw)

-- | Generate a makefile for ease of experimentation..
genMake :: String -> String -> Doc
genMake fn dn =
     text "# Makefile for" <+> nm <> text ", automatically generated by SBV. Do not edit!"
  $$ text ""
  $$ text "CC=gcc"
  $$ text "CCFLAGS=-Wall -O3 -DNDEBUG -fomit-frame-pointer"
  $$ text ""
  $$ text "all:" <+> nmd
  $$ text ""
  $$ nmo <> text ":" <+> fsep [nmc, nmh]
  $$ text "\t${CC} ${CCFLAGS}" <+> text "-c" <+> nmc <+> text "-o" <+> nmo
  $$ text ""
  $$ nmdo <> text ":" <+> nmdc
  $$ text "\t${CC} ${CCFLAGS}" <+> text "-c" <+> nmdc <+> text "-o" <+> nmdo
  $$ text ""
  $$ nmd <> text ":" <+> fsep [nmo, nmdo]
  $$ text "\t${CC} ${CCFLAGS}" <+> nmo <+> nmdo <+> text "-o" <+> nmd
  $$ text ""
  $$ text "clean:"
  $$ text "\trm -f" <+> nmdo <+> nmo
  $$ text ""
  $$ text "veryclean: clean"
  $$ text "\trm -f" <+> nmd
  $$ text ""
 where nm   = text fn
       nmd  = text dn
       nmh  = nm <> text ".h"
       nmc  = nm <> text ".c"
       nmo  = nm <> text ".o"
       nmdc = nmd <> text ".c"
       nmdo = nmd <> text ".o"

-- | Generate the header
genHeader :: String -> Doc -> Doc
genHeader fn signature =
     text "/* Header file for" <+> nm <> text ", automatically generated by SBV. Do not edit! */"
  $$ text ""
  $$ text "#ifndef" <+> tag
  $$ text "#define" <+> tag
  $$ text ""
  $$ text "#include <inttypes.h>"
  $$ text "#include <stdint.h>"
  $$ text ""
  $$ text "/* Unsigned bit-vectors */"
  $$ text "typedef uint8_t  SBool  ;"
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
  $$ text "/* Entry point prototype: */"
  $$ signature <> semi
  $$ text ""
  $$ text "#endif /*" <+> tag <+> text "*/"
  $$ text ""
 where nm  = text fn
       tag = text "__" <> nm <> text "__HEADER_INCLUDED__"

-- | Generate an example driver program
genDriver :: [Integer] -> String -> CType -> Doc
genDriver randVals fn (CType (inps, outs)) =
     text "/* Example driver program for" <+> nm <+> text "*/"
  $$ text "/* Automatically generated by SBV. Edit as you see fit! */"
  $$ text ""
  $$ text "#include <inttypes.h>"
  $$ text "#include <stdint.h>"
  $$ text "#include <stdio.h>"
  $$ text "#include" <+> doubleQuotes (nm <> text ".h")
  $$ text ""
  $$ text "int main(void)"
  $$ text "{"
  $$ text ""
  $$ nest 2 (   vcat (map (\p -> mkParam p <> semi) (if singleOut then [] else outs))
             $$ (if singleOut then empty else text "")
             $$ call
             $$ text ""
             $$ (case outs of
                   [(_, bsz)] ->   text "printf" <> parens (doubleQuotes (fcall <+> text "=" <+> specifier bsz <> text "\\n") <> comma <+> text "sbvResult") <> semi
                   _          ->   text "printf" <> parens (doubleQuotes (fcall <+> text "->\\n")) <> semi
                                 $$ vcat (map display outs))
             $$ text ""
             $$ text "return 0" <> semi)
  $$ text "}"
  $$ text ""
 where nm = text fn
       singleOut = case outs of
                    [_] -> True
                    _   -> False
       call = case outs of
                [(_, bs)] -> pprCWord bs <+> text "sbvResult" <+> text "=" <+> fcall <> semi
                _         -> fcall <> semi
       mkCVal (_, bsz@(b, sz)) r
         | not b = mkConst (abs r `mod` (2^sz))                bsz
         | True  = mkConst ((abs r `mod` (2^sz)) - (2^(sz-1))) bsz
       fcall = case outs of
                [_] -> nm <> parens (fsep (punctuate comma (zipWith mkCVal inps randVals)))
                _   -> nm <> parens (fsep (punctuate comma (zipWith mkCVal inps randVals ++ map (\ (n, _) -> text "&" <> text n) outs)))
       display (s, bsz) = text "printf" <> parens (doubleQuotes (text " " <+> text s <+> text "=" <+> specifier bsz <> text "\\n") <> comma <+> text s) <> semi

-- | Generate the C program
genCProg :: String -> Doc -> Result -> Doc
genCProg fn proto (Result inps consts tbls arrs uints axms asgns outs)
  | not (null arrs)  = tbd "User level arrays are currently not supported."
  | not (null uints) = tbd "Uninterpreted constants are currently not supported."
  | not (null axms)  = tbd "User given axioms are currently not supported."
  | True
  =  text "/*" <+> nm <> text ".c: automatically generated by SBV. Do not edit! */"
  $$ text ""
  $$ text "#include <inttypes.h>"
  $$ text "#include <stdint.h>"
  $$ text "#include" <+> doubleQuotes (nm <> text ".h")
  $$ text ""
  $$ proto
  $$ text "{"
  $+$ nest 2 (   vcat (map genInp inps)
              $$ vcat (map genTbl tbls)
              $$ genDefs asgns
              $$ genOuts outs)
  $$ text "}"
  $$ text ""
 where nm = text fn
       isConst s = isJust $ lookup s consts
       getConst s =  maybe (error ("SBV2C: Cannot find " ++ show s ++ " in the constants table")) id (lookup s consts)
       genInp :: NamedSymVar -> Doc
       genInp (sw@(SW bs _), n)
         | show s == n = empty
         | True        = mkParam (s, bs) <+> text "=" <+> text n <> semi
         where s = show sw
       genTbl :: ((Int, (Bool, Int), (Bool, Int)), [SW]) -> Doc
       genTbl ((i, _, (sg, sz)), elts)
         | all isConst elts = mkParam ("table" ++ show i, (sg, sz)) <> text "[] = {"
                              $$ nest 4 (fsep (punctuate comma (map (showConst . getConst) elts)))
                              $$ text "};"
         | True             = tbd $ "Tables (select) with non-constant elements are currently not supported"
       genDefs :: Pgm -> Doc
       genDefs = comment . text . show
       genOuts :: [SW] -> Doc
       genOuts = comment . text . show
       comment d = text "/*" $$ d $$ text "*/"
