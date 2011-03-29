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

module Data.SBV.Compilers.C(compileToC, compileToC') where

import Data.Char(isSpace)
import Data.Maybe(isJust)
import qualified Data.Foldable as F (toList)
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

-- Unexpected input, or things we will probably never support
die :: String -> a
die msg = error $ "SBV->C: Unexpected: " ++ msg

-- Unsupported features, or features TBD
tbd :: String -> a
tbd msg = error $ "SBV->C: Not yet supported: " ++ msg

-- | Given a symbolic computation, render it as an equivalent C program.
--
--    * First argument: States whether run-time-checks should be inserted for index-out-of-bounds or shifting-by-large values etc.
--      If `False`, such checks are ignored, gaining efficiency, at the cost of potential undefined behavior.
--
--    * Second argument is an optional directory name under which the files will be saved. If `Nothing`, the result
--      will be written to stdout. Use @`Just` \".\"@ for creating files in the current directory.
--
--    * The third argument is name of the function, which also forms the names of the C and header files.
--
--    * The fourth argument are the names of the arguments to be used and the names of the outputs, if any.
--       Provide as many arguments as you like, SBV will make up ones if you don't pass enough.
--
--    * The fifth and the final argument is the computation to be compiled.
--
-- Compilation will also generate a @Makefile@ and a sample driver program, which executes the program over random
-- input values.
compileToC :: SymExecutable f => Bool -> Maybe FilePath -> String -> [String] -> f -> IO ()
compileToC rtc mbDir fn extraNames f = do rands <- newStdGen >>= return . randoms
                                          codeGen SBVToC rands rtc mbDir fn extraNames f

-- | Alternative interface for generating C. The output driver program uses the specified values (first argument) instead of random values.
-- Also this version returns the generated files for further manipulation. (Useful mainly for generating regression tests.)
compileToC' :: SymExecutable f => [Integer] -> Bool -> String -> [String] -> f -> IO CgPgmBundle
compileToC' dvals = codeGen' SBVToC (dvals ++ repeat 0)

cgen :: [Integer] -> Bool -> String -> [String] -> Result -> CgPgmBundle
cgen randVals rtc nm extraNames sbvProg@(Result ins _ _ _ _ _ _ outs) = CgPgmBundle
        [ ("Makefile",  genMake   nm nmd)
        , (nm  ++ ".h", genHeader nm sig)
        , (nmd ++ ".c", genDriver randVals nm typ)
        , (nm  ++ ".c", genCProg  rtc nm sig sbvProg (map fst outputVars))
        ]
  where nmd = nm ++ "_driver"
        typ@(CType (_, outputVars)) = mkCType extraNames ins outs
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
                          [(_, bs)] -> (pprCWord False bs, [])
                          _         -> (text "void", map mkPParam outs)

mkParam, mkPParam :: (String, (Bool, Int)) -> Doc
mkParam  (n, bs) = pprCWord True  bs <+> text n
mkPParam (n, bs) = pprCWord False bs <+> text "*" <> text n

-- | Renders as "const SWord8 s0", etc. the first parameter is the width of the typefield
declSW :: Int -> SW -> Doc
declSW w sw@(SW sgsz _) = text "const" <+> pad (showCType sgsz) <+> text (show sw)
  where pad s = text $ s ++ take (w - length s) (repeat ' ')

-- | Renders as "s0", etc, or the corresponding constant
showSW :: [(SW, CW)] -> SW -> Doc
showSW consts sw
  | sw == falseSW                 = text "0"
  | sw == trueSW                  = text "1"
  | Just cw <- sw `lookup` consts = showConst cw
  | True                          = text $ show sw

-- | Words as it would be defined in the standard header stdint.h
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
mkConst i   (False,  1) = integer i
mkConst i t@(False,  8) = text (shex False True t i)
mkConst i t@(True,   8) = text (shex False True t i)
mkConst i t@(False, 16) = text (shex False True t i) <> text "U"
mkConst i t@(True,  16) = text (shex False True t i)
mkConst i t@(False, 32) = text (shex False True t i) <> text "UL"
mkConst i t@(True,  32) = text (shex False True t i) <> text "L"
mkConst i t@(False, 64) = text (shex False True t i) <> text "ULL"
mkConst i t@(True,  64) = text (shex False True t i) <> text "LL"
mkConst i   (True,  1)  = die $ "Signed 1-bit value " ++ show i
mkConst i   (s, sz)     = die $ "Constant " ++ show i ++ " at type " ++ (if s then "SInt" else "SWord") ++ show sz

-- | Show a constant
showConst :: CW -> Doc
showConst cw = mkConst (cwVal cw) (hasSign cw, sizeOf cw)

-- | Generate a makefile for ease of experimentation..
genMake :: String -> String -> Doc
genMake fn dn =
     text "# Makefile for" <+> nm <> text ". Automatically generated by SBV. Do not edit!"
  $$ text ""
  $$ text "CC=gcc"
  $$ text "CCFLAGS=-Wall -O3 -DNDEBUG -fomit-frame-pointer"
  $$ text ""
  $$ text "all:" <+> nmd
  $$ text ""
  $$ nmo <> text ":" <+> hsep [nmc, nmh]
  $$ text "\t${CC} ${CCFLAGS}" <+> text "-c" <+> nmc <+> text "-o" <+> nmo
  $$ text ""
  $$ nmdo <> text ":" <+> nmdc
  $$ text "\t${CC} ${CCFLAGS}" <+> text "-c" <+> nmdc <+> text "-o" <+> nmdo
  $$ text ""
  $$ nmd <> text ":" <+> hsep [nmo, nmdo]
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
     text "/* Header file for" <+> nm <> text ". Automatically generated by SBV. Do not edit! */"
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

sepIf :: Bool -> Doc
sepIf b = if b then text "" else empty

-- | Generate an example driver program
genDriver :: [Integer] -> String -> CType -> Doc
genDriver randVals fn (CType (inps, outs)) =
     text "/* Example driver program for" <+> nm <> text ". */"
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
  $$ nest 2 (   vcat (map (\ (n, bs) -> pprCWord False bs <+> text n <> semi) (if singleOut then [] else outs))
             $$ sepIf (not singleOut)
             $$ call
             $$ text ""
             $$ (case outs of
                   [(n, bsz)] ->   text "printf" <> parens (printQuotes (fcall <+> text "=" <+> specifier bsz <> text "\\n") <> comma <+> text n) <> semi
                   _          ->   text "printf" <> parens (printQuotes (fcall <+> text "->\\n")) <> semi
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
                [(n, bs)] -> pprCWord True bs <+> text n <+> text "=" <+> fcall <> semi
                _         -> fcall <> semi
       mkCVal (_, bsz@(b, sz)) r
         | not b = mkConst (abs r `mod` (2^sz))                bsz
         | True  = mkConst ((abs r `mod` (2^sz)) - (2^(sz-1))) bsz
       fcall = case outs of
                [_] -> nm <> parens (fsep (punctuate comma (zipWith mkCVal inps randVals)))
                _   -> nm <> parens (fsep (punctuate comma (zipWith mkCVal inps randVals ++ map (\ (n, _) -> text "&" <> text n) outs)))
       display (s, bsz) = text "printf" <> parens (printQuotes (text " " <+> text s <+> text "=" <+> specifier bsz <> text "\\n") <> comma <+> text s) <> semi

-- | Generate the C program
genCProg :: Bool -> String -> Doc -> Result -> [String] -> Doc
genCProg rtc fn proto (Result inps preConsts tbls arrs uints axms asgns outs) outputVars
  | not (null arrs)  = tbd "User specified arrays"
  | not (null uints) = tbd "Uninterpreted constants"
  | not (null axms)  = tbd "User given axioms"
  | True
  =  text "/* File:" <+> doubleQuotes (nm <> text ".c") <> text ". Automatically generated by SBV. Do not edit! */"
  $$ text ""
  $$ text "#include <inttypes.h>"
  $$ text "#include <stdint.h>"
  $$ text "#include" <+> doubleQuotes (nm <> text ".h")
  $$ text ""
  $$ proto
  $$ text "{"
  $$ text ""
  $$ nest 2 (   vcat (map genInp inps)
             $$ vcat (merge (map genTbl tbls) (map genAsgn assignments))
             $$ sepIf (not (null assignments) || not (null tbls))
             $$ genOuts outs)
  $$ text "}"
  $$ text ""
 where nm = text fn
       assignments = F.toList asgns
       typeWidth = getMax 0 [len (hasSign s, sizeOf s) | (s, _) <- assignments]
                where len (False, 1) = 5 -- SBool
                      len (False, n) = 5 + length (show n) -- SWordN
                      len (True,  n) = 4 + length (show n) -- SIntN
                      getMax 7 _      = 7  -- 7 is the max we can get with SWord64, so don't bother looking any further
                      getMax m []     = m
                      getMax m (x:xs) = getMax (m `max` x) xs
       consts = (falseSW, falseCW) : (trueSW, trueCW) : preConsts
       isConst s = isJust (lookup s consts)
       genInp :: NamedSymVar -> Doc
       genInp (sw, n)
         | show sw == n = empty  -- no aliasing, so no need to assign
         | True         = declSW typeWidth sw <+> text "=" <+> text n <> semi
       genTbl :: ((Int, (Bool, Int), (Bool, Int)), [SW]) -> (Int, Doc)
       genTbl ((i, _, (sg, sz)), elts) =  (location, static <+> mkParam ("table" ++ show i, (sg, sz)) <> text "[] = {"
                                                     $$ nest 4 (fsep (punctuate comma (align (map (showSW consts) elts))))
                                                     $$ text "};")
         where static   = if location == -1 then text "static" else empty
               location = maximum (-1 : map getNodeId elts)
       getNodeId s@(SW _ (NodeId n)) | isConst s = -1
                                     | True      = n
       genAsgn :: (SW, SBVExpr) -> (Int, Doc)
       genAsgn (sw, n) = (getNodeId sw, declSW typeWidth sw <+> text "=" <+> ppExpr rtc consts n <> semi)
       genOuts :: [SW] -> Doc
       genOuts [sw] = text "return" <+> showSW consts sw <> semi
       genOuts os
         | length os /= length outputVars = die $ "Mismatched outputs: " ++ show (os, outputVars)
         | True                           = vcat (zipWith assignOut outputVars os)
         where assignOut v sw = text "*" <> text v <+> text "=" <+> showSW consts sw <> semi
       -- merge tables intermixed with assignments, paying attention to putting tables as
       -- early as possible.. Note that the assignment list (second argument) is sorted on its order
       merge :: [(Int, Doc)] -> [(Int, Doc)] -> [Doc]
       merge []               as                  = map snd as
       merge ts               []                  = map snd ts
       merge ts@((i, t):trest) as@((i', a):arest)
         | i < i'                                 = t : merge trest as
         | True                                   = a : merge ts arest
       -- Align a bunch of docs to occupy the exact same length by padding in the left by space
       -- this is ugly and inefficient, but easy to code..
       align :: [Doc] -> [Doc]
       align ds = map (text . pad) ss
         where ss    = map render ds
               l     = maximum (0 : map length ss)
               pad s = take (l - length s) (repeat ' ') ++ s

ppExpr :: Bool -> [(SW, CW)] -> SBVExpr -> Doc
ppExpr rtc consts (SBVApp op opArgs) = p op (map (showSW consts) opArgs)
  where cBinOps = [ (Plus, "+"), (Times, "*"), (Minus, "-"), (Quot, "/"), (Rem, "%")
                  , (Equal, "=="), (NotEqual, "!=")
                  , (LessThan, "<"), (GreaterThan, ">"), (LessEq, "<="), (GreaterEq, ">=")
                  , (And, "&"), (Or, "|"), (XOr, "^")
                  ]
        p (ArrRead _)       _ = tbd $ "User specified arrays (ArrRead)"
        p (ArrEq _ _)       _ = tbd $ "User specified arrays (ArrEq)"
        p (Uninterpreted s) _ = tbd $ "Uninterpreted constants (" ++ show s ++ ")"
        p (Extract i j) [a]   = extract i j (let s = head opArgs in (hasSign s, sizeOf s)) a
        p Join [a, b]         = join (let (s1 : s2 : _) = opArgs in ((hasSign s1, sizeOf s1), (hasSign s2, sizeOf s2), a, b))
        p (Rol i) [a]         = rotate True  i a (let s = head opArgs in (hasSign s, sizeOf s))
        p (Ror i) [a]         = rotate False i a (let s = head opArgs in (hasSign s, sizeOf s))
        p (Shl i) [a]         = shift True  i a (let s = head opArgs in (hasSign s, sizeOf s))
        p (Shr i) [a]         = shift False i a (let s = head opArgs in (hasSign s, sizeOf s))
        p Not [a] = text "~" <> a
        p Ite [a, b, c] = a <+> text "?" <+> b <+> text ":" <+> c
        p (LkUp (t, (as, at), _, len) ind def) []
          | not rtc                    = lkUp -- ignore run-time-checks per user request
          | needsCheckL && needsCheckR = cndLkUp checkBoth
          | needsCheckL                = cndLkUp checkLeft
          | needsCheckR                = cndLkUp checkRight
          | True                       = lkUp
          where [index, defVal] = map (showSW consts) [ind, def]
                lkUp = text "table" <> int t <> brackets (showSW consts ind)
                cndLkUp cnd = cnd <+> text "?" <+> defVal <+> text ":" <+> lkUp
                checkLeft  = index <+> text "< 0"
                checkRight = index <+> text ">=" <+> int len
                checkBoth  = parens (checkLeft <+> text "||" <+> checkRight)
                (needsCheckL, needsCheckR) | as   = (True,  (2::Integer)^(at-1)-1  >= (fromIntegral len))
                                           | True = (False, (2::Integer)^(at)  -1  >= (fromIntegral len))
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
        extract 63 32 (False, 64) a = text "(SWord32)" <+> (parens (a <+> text ">> 32"))
        extract 31  0 (False, 64) a = text "(SWord32)" <+> a
        extract 31 16 (False, 32) a = text "(SWord16)" <+> (parens (a <+> text ">> 16"))
        extract 15  0 (False, 32) a = text "(SWord16)" <+> a
        extract 15  8 (False, 16) a = text "(SWord8)"  <+> (parens (a <+> text ">> 8"))
        extract  7  0 (False, 16) a = text "(SWord8)"  <+> a
        extract  i  j (sg, sz)    _ = tbd $ "extract with " ++ show (i, j, (sg, sz))
        -- TBD: ditto here for join, just like extract above
        join ((False,  8), (False,  8), a, b) = parens ((parens (text "(SWord16)" <+> a)) <+> text "<< 8")  <+> text "|" <+> parens (text "(SWord16)" <+> b)
        join ((False, 16), (False, 16), a, b) = parens ((parens (text "(SWord32)" <+> a)) <+> text "<< 16") <+> text "|" <+> parens (text "(SWord32)" <+> b)
        join ((False, 32), (False, 32), a, b) = parens ((parens (text "(SWord64)" <+> a)) <+> text "<< 32") <+> text "|" <+> parens (text "(SWord64)" <+> b)
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
