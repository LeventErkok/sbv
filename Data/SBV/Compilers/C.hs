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

module Data.SBV.Compilers.C(compileToC) where

import Data.SBV.BitVectors.Data (Outputtable(..), Result)
import Data.SBV.Compilers.CodeGen

-- token for the target language
data SBVToC = SBVToC

-- | Given a symbolic computation, render it as an equivalent
--   C program. The first argument is an optional directory name
--   under which the files will be saved. If `Nothing`, the result
--   will be written to stdout. Use @`Just` \".\"@ for creating files in
--   the current directory. The second argument is name of the function,
--   which also forms the names of the C and header files. The third argument
--   is the names of the arguments to be used and the names of the outputs, if any.
--   (Provide as many arguments as you like, SBV will make up ones if you don't pass
--   enough.) The final argument is the computation to be compiled.
compileToC :: (CgArgs a, Outputtable b) => Maybe FilePath -> String -> [String] -> (a -> b) -> IO ()
compileToC = codeGen SBVToC

instance SBVTarget SBVToC where
  targetName _ = "C"
  translate _  = cgen

cgen :: String -> Result -> [(FilePath, [String])]
cgen nm sbvProg = [(nm ++ ".c", lines (show sbvProg))]
