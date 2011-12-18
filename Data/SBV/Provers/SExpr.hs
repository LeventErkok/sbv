-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.SExpr
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Parsing of S-expressions (mainly used for parsing Yices output)
-----------------------------------------------------------------------------

module Data.SBV.Provers.SExpr where

import Control.Monad.Error ()             -- for Monad (Either String) instance
import Data.Char           (isDigit, ord)
import Numeric             (readInt, readDec, readHex)

data SExpr = SCon String
           | SNum Integer
           | SApp [SExpr]

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
                              return (SApp f, r)
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
        pTok ('0':'b':r)       = mkNum $ readInt 2 (`elem` "01") (\c -> ord c - ord '0') r
        pTok ('b':'v':r)       = mkNum $ readDec (takeWhile (/= '[') r)
        pTok ('#':'b':r)       = mkNum $ readInt 2 (`elem` "01") (\c -> ord c - ord '0') r
        pTok ('#':'x':r)       = mkNum $ readHex r
        pTok n | all isDigit n = mkNum $ readDec n
        pTok n                 = return $ SCon n
        mkNum [(n, "")] = return $ SNum n
        mkNum _         = die "cannot read number"
