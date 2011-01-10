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

import Control.Monad.Error() -- for Monad (Either String) instance
import Data.Char (isDigit, ord)
import Numeric

data SExpr = S_Con String
           | S_Num Integer
           | S_App [SExpr]

parseSExpr :: String -> Either String SExpr
parseSExpr inp = do (sexp, []) <- parse inpToks
                    return sexp
  where inpToks = let cln ""          sofar = sofar
                      cln ('(':r)     sofar = cln r (" ( " ++ sofar)
                      cln (')':r)     sofar = cln r (" ) " ++ sofar)
                      cln (':':':':r) sofar = cln r (" :: " ++ sofar)
                      cln (c:r)       sofar = cln r (c:sofar)
                  in reverse (map reverse (words (cln inp "")))
        parse []         = fail "ran out of tokens"
        parse ("(":toks) = do (f, r) <- parseApp toks []
                              return (S_App f, r)
        parse (")":_)    = fail "extra tokens after close paren"
        parse [tok]      = do t <- pTok tok
                              return (t, [])
        parse _          = fail "ill-formed s-expr"
        parseApp []         _     = fail "failed to grab s-expr application"
        parseApp (")":toks) sofar = return (reverse sofar, toks)
        parseApp ("(":toks) sofar = do (f, r) <- parse ("(":toks)
                                       parseApp r (f : sofar)
        parseApp (tok:toks) sofar = do t <- pTok tok
                                       parseApp toks (t : sofar)
        pTok ('0':'b':r)       = mkNum $ readInt 2 (`elem` "01") (\c -> ord c - ord '0') r
        pTok ('b':'v':r)       = mkNum $ readDec (takeWhile (/= '[') r)
        pTok n | all isDigit n = mkNum $ readDec n
        pTok n                 = return $ S_Con $ n
        mkNum [(n, "")] = return $ S_Num n
        mkNum _         = fail "cannot read number"
