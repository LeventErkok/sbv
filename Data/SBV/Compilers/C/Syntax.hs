-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.Syntax
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Safe rendering of diagnostic text in generated C source.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.Syntax (cCommentText, cStringLiteral) where

import qualified Data.ByteString as BS
import Data.Char (chr, isControl, ord)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Numeric (showOct)
import Text.PrettyPrint.HughesPJ (Doc, doubleQuotes, text)

-- | Render comment contents without allowing comment delimiters, line splices,
-- trigraphs, or embedded control characters to affect the surrounding C source.
-- Octal spellings here are readable text, not escapes interpreted by C comments.
cCommentText :: String -> Doc
cCommentText = text . concatMap escape
 where escape '*'  = "\\052"
       escape '\\' = "\\134"
       escape '?'  = "\\077"
       escape '\n' = "\n"
       escape '\t' = "\t"
       escape c
         | isControl c = '\\' : showOct (ord c) ""
         | True        = [c]

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
