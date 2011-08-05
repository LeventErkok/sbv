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

import Data.Char (isSpace)
import Data.Maybe (isJust)
import qualified Data.Foldable as F (toList)
import Text.PrettyPrint.HughesPJ
import System.FilePath (takeBaseName, replaceExtension)
import System.Random

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum(shex)
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
compileToC' nm f = do rands <- newStdGen >>= return . randoms
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

-- Unsupported features, or features TBD
tbd :: String -> a
tbd msg = error $ "SBV->C: Not yet supported: " ++ msg

cgen :: Bool -> [Integer] -> String -> CgState -> Result -> CgPgmBundle
cgen rtc randVals nm st sbvProg = CgPgmBundle
        [ ("Makefile",  (CgMakefile,     [genMake   nm nmd]))
        , (nm  ++ ".h", (CgHeader [sig], [genHeader nm [sig]]))
        , (nmd ++ ".c", (CgDriver,       genDriver randVals nm ins outs mbRet))
        , (nm  ++ ".c", (CgSource,       genCProg rtc nm sig sbvProg ins outs mbRet))
        ]
  where nmd = nm ++ "_driver"
        sig = pprCFunHeader nm ins outs mbRet
        ins      = cgInputs st
        outs     = cgOutputs st
        mbRet    = case cgReturns st of
                     []           -> Nothing
                     [CgAtomic o] -> Just o
                     [CgArray _]  -> tbd $ "Non-atomic return values"
                     _            -> tbd $ "Multiple return values"

-- | Pretty print a functions type. If there is only one output, we compile it
-- as a function that returns that value. Otherwise, we compile it as a void function
-- that takes return values as pointers to be updated.
pprCFunHeader :: String -> [(String, CgVal)] -> [(String, CgVal)] -> Maybe SW -> Doc
pprCFunHeader fn ins outs mbRet = retType <+> text fn <> parens (fsep (punctuate comma (map mkParam ins ++ map mkPParam outs)))
  where retType = case mbRet of
                   Nothing -> text "void"
                   Just sw -> pprCWord False (hasSign sw, sizeOf sw)

mkParam, mkPParam :: (String, CgVal) -> Doc
mkParam  (n, CgAtomic sw)     = let sgsz = (hasSign sw, sizeOf sw) in pprCWord True  sgsz <+> text n
mkParam  (_, CgArray  [])     = die $ "mkParam: CgArray with no elements!"
mkParam  (n, CgArray  (sw:_)) = let sgsz = (hasSign sw, sizeOf sw) in pprCWord True  sgsz <+> text "*" <> text n
mkPParam (n, CgAtomic sw)     = let sgsz = (hasSign sw, sizeOf sw) in pprCWord False sgsz <+> text "*" <> text n
mkPParam (_, CgArray  [])     = die $ "mPkParam: CgArray with no elements!"
mkPParam (n, CgArray  (sw:_)) = let sgsz = (hasSign sw, sizeOf sw) in pprCWord False sgsz <+> text "*" <> text n

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
showConst :: CW -> Doc
showConst cw = mkConst (cwVal cw) (hasSign cw, sizeOf cw)

-- | Generate a makefile
genMake :: String -> String -> Doc
genMake fn dn =
     text "# Makefile for" <+> nm <> text ". Automatically generated by SBV. Do not edit!"
  $$ text ""
  $$ text "# include any user-defined .mk file in the current directory."
  $$ text "-include *.mk"
  $$ text ""
  $$ text "CC=gcc"
  $$ text "CCFLAGS?=-Wall -O3 -DNDEBUG -fomit-frame-pointer"
  $$ text ""
  $$ text "all:" <+> nmd
  $$ text ""
  $$ nmo <> text (": " ++ ppSameLine (hsep [nmc, nmh]))
  $$ text "\t${CC} ${CCFLAGS}" <+> text "-c $< -o $@"
  $$ text ""
  $$ nmdo <> text ":" <+> nmdc
  $$ text "\t${CC} ${CCFLAGS}" <+> text "-c $< -o $@"
  $$ text ""
  $$ nmd <> text (": " ++ ppSameLine (hsep [nmo, nmdo]))
  $$ text "\t${CC} ${CCFLAGS}" <+> text "$^ -o $@"
  $$ text ""
  $$ text "clean:"
  $$ text "\trm -f *.o"
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
genHeader :: String -> [Doc] -> Doc
genHeader fn sigs =
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
  $$ text ("/* Entry point prototype" ++ plu ++ ": */")
  $$ vcat (map (<> semi) sigs)
  $$ text ""
  $$ text "#endif /*" <+> tag <+> text "*/"
  $$ text ""
 where nm  = text fn
       tag = text "__" <> nm <> text "__HEADER_INCLUDED__"
       plu = if length sigs /= 1 then "s" else ""

sepIf :: Bool -> Doc
sepIf b = if b then text "" else empty

-- | Generate an example driver program
genDriver :: [Integer] -> String -> [(String, CgVal)] -> [(String, CgVal)] -> Maybe SW -> [Doc]
genDriver randVals fn inps outs mbRet = [pre, header, body, post]
 where pre    =  text "/* Example driver program for" <+> nm <> text ". */"
              $$ text "/* Automatically generated by SBV. Edit as you see fit! */"
              $$ text ""
              $$ text "#include <inttypes.h>"
              $$ text "#include <stdint.h>"
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
                              Just sw -> text "printf" <> parens (printQuotes (fcall <+> text "=" <+> specifier (hasSign sw, sizeOf sw) <> text "\\n")
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
       matchRands _      []                                   = []
       matchRands []     _                                    = die $ "Run out of driver values!"
       matchRands (r:rs) ((n, CgAtomic sw)              : cs) = ([mkRVal sw r], n, CgAtomic sw) : matchRands rs cs
       matchRands _      ((n, CgArray [])               : _ ) = die $ "Unsupported empty array input " ++ show n
       matchRands rs     ((n, a@(CgArray sws@((sw:_)))) : cs)
          | length frs /= l                                   = die $ "Run out of driver values!"
          | True                                              = (map (mkRVal sw) frs, n, a) : matchRands srs cs
          where l          = length sws
                (frs, srs) = splitAt l rs
       mkRVal sw r = mkConst ival sgsz
         where sgsz@(sg, sz) = (hasSign sw, sizeOf sw)
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
       mkInp (vs, n, CgArray sws@(sw:_)) =  pprCWord True (hasSign sw, sizeOf sw) <+> text n <> brackets (int (length sws)) <+> text "= {"
                                                      $$ nest 4 (fsep (punctuate comma (align vs)))
                                                      $$ text "};"
                                         $$ text ""
                                         $$ text "printf" <> parens (printQuotes (text "Contents of input array" <+> text n <> text ":\\n")) <> semi
                                         $$ display (n, CgArray sws)
                                         $$ text ""
       mkOut (v, CgAtomic sw)            = let sgsz = (hasSign sw, sizeOf sw) in pprCWord False sgsz <+> text v <> semi
       mkOut (v, CgArray [])             = die $ "Unsupported empty array value for " ++ show v
       mkOut (v, CgArray sws@(sw:_))     = pprCWord False (hasSign sw, sizeOf sw) <+> text v <> brackets (int (length sws)) <> semi
       resultVar = text "__result"
       call = case mbRet of
                Nothing -> fcall <> semi
                Just sw -> pprCWord True (hasSign sw, sizeOf sw) <+> resultVar <+> text "=" <+> fcall <> semi
       fcall = nm <> parens (fsep (punctuate comma (map mkCVal pairedInputs ++ map mkOVal outs)))
       mkCVal ([v], _, CgAtomic{}) = v
       mkCVal (vs,  n, CgAtomic{}) = die $ "Unexpected driver value computed for " ++ show n ++ render (hcat vs)
       mkCVal (_,   n, CgArray{})  = text n
       mkOVal (n, CgAtomic{})      = text "&" <> text n
       mkOVal (n, CgArray{})       = text n
       display (n, CgAtomic sw)         = text "printf" <> parens (printQuotes (text " " <+> text n <+> text "=" <+> specifier (hasSign sw, sizeOf sw)
                                                                                <> text "\\n") <> comma <+> text n) <> semi
       display (n, CgArray [])         =  die $ "Unsupported empty array value for " ++ show n
       display (n, CgArray sws@(sw:_)) =   text "int" <+> nctr <> semi
                                        $$ text "for(" <> nctr <+> text "= 0; " <+> nctr <+> text "<" <+> int (length sws) <+> text "; ++" <> nctr <> text ")"
                                        $$ nest 2 (text "printf" <> parens (printQuotes (text " " <+> entrySpec <+> text "=" <+> spec <> text "\\n")
                                                                 <> comma <+> nctr <+> comma <> entry) <> semi)
                  where nctr      = text n <> text "_ctr"
                        entry     = text n <> text "[" <> nctr <> text "]"
                        entrySpec = text n <> text "[%d]"
                        spec      = specifier (hasSign sw, sizeOf sw)

-- | Generate the C program
genCProg :: Bool -> String -> Doc -> Result -> [(String, CgVal)] -> [(String, CgVal)] -> Maybe SW -> [Doc]
genCProg rtc fn proto (Result _ preConsts tbls arrs uints axms asgns _) inVars outVars mbRet
  | not (null arrs)  = tbd "User specified arrays"
  | not (null uints) = tbd "Uninterpreted constants"
  | not (null axms)  = tbd "User given axioms"
  | True
  = [pre, header, post]
 where pre    = text "/* File:" <+> doubleQuotes (nm <> text ".c") <> text ". Automatically generated by SBV. Do not edit! */"
              $$ text ""
              $$ text "#include <inttypes.h>"
              $$ text "#include <stdint.h>"
       header = text "#include" <+> doubleQuotes (nm <> text ".h")
       post   =  text ""
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
       typeWidth = getMax 0 [len (hasSign s, sizeOf s) | (s, _) <- assignments]
                where len (False, 1) = 5 -- SBool
                      len (False, n) = 5 + length (show n) -- SWordN
                      len (True,  n) = 4 + length (show n) -- SIntN
                      getMax 7 _      = 7  -- 7 is the max we can get with SWord64, so don't bother looking any further
                      getMax m []     = m
                      getMax m (x:xs) = getMax (m `max` x) xs
       consts = (falseSW, falseCW) : (trueSW, trueCW) : preConsts
       isConst s = isJust (lookup s consts)
       genIO :: Bool -> (String, CgVal) -> [Doc]
       genIO True  (cNm, CgAtomic sw) = [declSW typeWidth sw  <+> text "=" <+> text cNm         <> semi]
       genIO False (cNm, CgAtomic sw) = [text "*" <> text cNm <+> text "=" <+> showSW consts sw <> semi]
       genIO isInp (cNm, CgArray sws) = zipWith genElt sws [(0::Int)..]
         where genElt sw i
                 | isInp = declSW typeWidth sw <+> text "=" <+> text entry       <> semi
                 | True  = text entry          <+> text "=" <+> showSW consts sw <> semi
                 where entry = cNm ++ "[" ++ show i ++ "]"
       mkRet sw = text "return" <+> showSW consts sw <> semi
       genTbl :: ((Int, (Bool, Int), (Bool, Int)), [SW]) -> (Int, Doc)
       genTbl ((i, _, (sg, sz)), elts) =  (location, static <+> pprCWord True (sg, sz) <+> text ("table" ++ show i) <> text "[] = {"
                                                     $$ nest 4 (fsep (punctuate comma (align (map (showSW consts) elts))))
                                                     $$ text "};")
         where static   = if location == -1 then text "static" else empty
               location = maximum (-1 : map getNodeId elts)
       getNodeId s@(SW _ (NodeId n)) | isConst s = -1
                                     | True      = n
       genAsgn :: (SW, SBVExpr) -> (Int, Doc)
       genAsgn (sw, n) = (getNodeId sw, declSW typeWidth sw <+> text "=" <+> ppExpr rtc consts n <> semi)
       -- merge tables intermixed with assignments, paying attention to putting tables as
       -- early as possible.. Note that the assignment list (second argument) is sorted on its order
       merge :: [(Int, Doc)] -> [(Int, Doc)] -> [Doc]
       merge []               as                  = map snd as
       merge ts               []                  = map snd ts
       merge ts@((i, t):trest) as@((i', a):arest)
         | i < i'                                 = t : merge trest as
         | True                                   = a : merge ts arest

ppExpr :: Bool -> [(SW, CW)] -> SBVExpr -> Doc
ppExpr rtc consts (SBVApp op opArgs) = p op (map (showSW consts) opArgs)
  where cBinOps = [ (Plus, "+"), (Times, "*"), (Minus, "-")
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
        extract 63 32 (False, 64) a = text "(SWord32)" <+> (parens (a <+> text ">> 32"))
        extract 31  0 (False, 64) a = text "(SWord32)" <+> a
        extract 31 16 (False, 32) a = text "(SWord16)" <+> (parens (a <+> text ">> 16"))
        extract 15  0 (False, 32) a = text "(SWord16)" <+> a
        extract 15  8 (False, 16) a = text "(SWord8)"  <+> (parens (a <+> text ">> 8"))
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

-- Align a bunch of docs to occupy the exact same length by padding in the left by space
-- this is ugly and inefficient, but easy to code..
align :: [Doc] -> [Doc]
align ds = map (text . pad) ss
  where ss    = map render ds
        l     = maximum (0 : map length ss)
        pad s = take (l - length s) (repeat ' ') ++ s

-- | Merge a bunch of bundles to generate code for a library
mergeToLib :: String -> [CgPgmBundle] -> CgPgmBundle
mergeToLib libName bundles = CgPgmBundle $ sources ++ [libHeader, libDriver, libMake]
  where files       = concat [fs | CgPgmBundle fs <- bundles]
        sigs        = concat [ss | (_, (CgHeader ss, _)) <- files]
        drivers     = [ds | (_, (CgDriver, ds)) <- files]
        sources     = [(f, (CgSource, [pre, libHInclude, post])) | (f, (CgSource, [pre, _, post])) <- files]
        sourceNms   = map fst sources
        libHeader   = (libName ++ ".h", (CgHeader sigs, [genHeader libName sigs]))
        libHInclude = text "#include" <+> text (show (libName ++ ".h"))
        libMake     = ("Makefile", (CgMakefile, [genLibMake libName sourceNms]))
        libDriver   = (libName ++ "_driver.c", (CgDriver, mergeDrivers libName libHInclude (zip (map takeBaseName sourceNms) drivers)))

-- | Create a Makefile for the library
genLibMake :: String -> [String] -> Doc
genLibMake libName fs =
     text "# Makefile for" <+> nm <> text ". Automatically generated by SBV. Do not edit!"
  $$ text ""
  $$ text "# include any user-defined .mk file in the current directory."
  $$ text "-include *.mk"
  $$ text ""
  $$ text "CC=gcc"
  $$ text "CCFLAGS?=-Wall -O3 -DNDEBUG -fomit-frame-pointer"
  $$ text "AR=ar"
  $$ text "ARFLAGS=cr"
  $$ text ""
  $$ text ("all: " ++ unwords [liba, libd])
  $$ text ""
  $$ text liba <> text (": " ++ unwords os)
  $$ text "\t${AR} ${ARFLAGS} $@ $^"
  $$ text ""
  $$ text libd <> text (": " ++ unwords [libd ++ ".c", libh])
  $$ text ("\t${CC} ${CCFLAGS} $< -o $@ " ++ liba)
  $$ text ""
  $$ vcat (zipWith mkObj os fs)
  $$ text "clean:"
  $$ text "\trm -f *.o"
  $$ text ""
  $$ text "veryclean: clean"
  $$ text "\trm -f" <+> text (unwords [liba, libd])
  $$ text ""
 where nm = text libName
       liba = libName ++ ".a"
       libh = libName ++ ".h"
       libd = libName ++ "_driver"
       os   = map (flip replaceExtension ".o") fs
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
                 lsep = take (length tag) (repeat '=')
                 psep = "printf(\"" ++ lsep ++ "\\n\");"
