-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.SExpr
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Parsing of S-expressions (mainly used for parsing SMT-Lib get-value output)
-----------------------------------------------------------------------------

module Data.SBV.Provers.SExpr where

import Control.Monad.Error ()             -- for Monad (Either String) instance
import Data.Char           (isDigit, ord)
import Data.Ratio
import Numeric             (readInt, readDec, readHex)

import Data.SBV.BitVectors.AlgReals

-- | ADT S-Expression format, suitable for representing get-model output of SMT-Lib
data SExpr = SCon  String
           | SNum  Integer
           | SReal AlgReal
           | SApp  [SExpr]

-- | Parse a string into an SExpr, potentially failing with an error message
parseSExpr :: String -> Either String SExpr
parseSExpr inp = do (sexp, []) <- parse inpToks
                    return sexp
  where inpToks = let cln ""          sofar = sofar
                      cln ('(':r)     sofar = cln r (" ( " ++ sofar)
                      cln (')':r)     sofar = cln r (" ) " ++ sofar)
                      cln (':':':':r) sofar = cln r (" :: " ++ sofar)
                      cln (c:r)       sofar = cln r (c:sofar)
                  in reverse (map reverse (words (cln inp "")))
        die w = fail $  "SBV.Provers.SExpr: Failed to parse S-Expr: " ++ w
                     ++ "\n*** Input : <" ++ inp ++ ">"
        parse []         = die "ran out of tokens"
        parse ("(":toks) = do (f, r) <- parseApp toks []
                              return (cvt (SApp f), r)
        parse (")":_)    = die "extra tokens after close paren"
        parse [tok]      = do t <- pTok tok
                              return (t, [])
        parse _          = die "ill-formed s-expr"
        parseApp []         _     = die "failed to grab s-expr application"
        parseApp (")":toks) sofar = return (reverse sofar, toks)
        parseApp ("(":toks) sofar = do (f, r) <- parse ("(":toks)
                                       parseApp r (f : sofar)
        parseApp (tok:toks) sofar = do t <- pTok tok
                                       parseApp toks (t : sofar)
        pTok ('0':'b':r)          = mkNum $ readInt 2 (`elem` "01") (\c -> ord c - ord '0') r
        pTok ('b':'v':r)          = mkNum $ readDec (takeWhile (/= '[') r)
        pTok ('#':'b':r)          = mkNum $ readInt 2 (`elem` "01") (\c -> ord c - ord '0') r
        pTok ('#':'x':r)          = mkNum $ readHex r
        pTok n
          | not (null n) && isDigit (head n)
          = if '.' `elem` n
            then let (a, '.':b) = break (== '.') n in getReal (a, b)
            else mkNum  $ readDec n
        pTok n                 = return $ SCon n
        mkNum [(n, "")] = return $ SNum n
        mkNum _         = die "cannot read number"
        getReal (n, d)
          | all isDigit (n ++ d) = let x :: Integer
                                       x = read (n++d)
                                   in return $ SReal $ fromRational $ x % 10 ^ length d
          | True                 = die "cannot read rational"
        -- simplify numbers
        cvt (SApp [SCon "/", SReal a, SReal b]) = SReal (a / b)
        cvt (SApp [SCon "/", SReal a, SNum  b]) = SReal (a             / fromInteger b)
        cvt (SApp [SCon "/", SNum  a, SReal b]) = SReal (fromInteger a /             b)
        cvt (SApp [SCon "/", SNum  a, SNum  b]) = SReal (fromInteger a / fromInteger b)
        cvt (SApp [SCon "-", SReal a])          = SReal (-a)
        cvt (SApp [SCon "-", SNum a])           = SNum  (-a)
        cvt x                                   = x
