-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.SExpr
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Parsing of S-expressions (mainly used for parsing SMT-Lib get-value output)
-----------------------------------------------------------------------------

module Data.SBV.Provers.SExpr where

import Control.Monad.Error ()             -- for Monad (Either String) instance
import Data.Char           (isDigit, ord)
import Data.List           (isPrefixOf)
import Numeric             (readInt, readDec, readHex)

import Data.SBV.BitVectors.AlgReals

-- | ADT S-Expression format, suitable for representing get-model output of SMT-Lib
data SExpr = SCon  String
           | SNum  Integer
           | SReal AlgReal
           | SApp  [SExpr]
           deriving Show

-- | Parse a string into an SExpr, potentially failing with an error message
parseSExpr :: String -> Either String SExpr
parseSExpr inp = do (sexp, extras) <- parse inpToks
                    if null extras
                       then return sexp
                       else die "Extra tokens after valid input"
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
                              f' <- cvt (SApp f)
                              return (f', r)
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
        pTok "false"              = return $ SNum 0
        pTok "true"               = return $ SNum 1
        pTok ('0':'b':r)          = mkNum $ readInt 2 (`elem` "01") (\c -> ord c - ord '0') r
        pTok ('b':'v':r)          = mkNum $ readDec (takeWhile (/= '[') r)
        pTok ('#':'b':r)          = mkNum $ readInt 2 (`elem` "01") (\c -> ord c - ord '0') r
        pTok ('#':'x':r)          = mkNum $ readHex r
        pTok n
          | not (null n) && isDigit (head n)
          = if '.' `elem` n then getReal n
            else mkNum  $ readDec n
        pTok n                 = return $ SCon n
        mkNum [(n, "")] = return $ SNum n
        mkNum _         = die "cannot read number"
        getReal n = return $ SReal $ mkPolyReal (Left (exact, n'))
          where exact = not ("?" `isPrefixOf` reverse n)
                n' | exact = n
                   | True  = init n
        -- simplify numbers and root-obj values
        cvt (SApp [SCon "/", SReal a, SReal b])                    = return $ SReal (a / b)
        cvt (SApp [SCon "/", SReal a, SNum  b])                    = return $ SReal (a             / fromInteger b)
        cvt (SApp [SCon "/", SNum  a, SReal b])                    = return $ SReal (fromInteger a /             b)
        cvt (SApp [SCon "/", SNum  a, SNum  b])                    = return $ SReal (fromInteger a / fromInteger b)
        cvt (SApp [SCon "-", SReal a])                             = return $ SReal (-a)
        cvt (SApp [SCon "-", SNum a])                              = return $ SNum  (-a)
        -- bit-vector value as CVC4 prints: (_ bv0 16) for instance
        cvt (SApp [SCon "_", SNum a, SNum _b])                     = return $ SNum a
        cvt (SApp [SCon "root-obj", SApp (SCon "+":trms), SNum k]) = do ts <- mapM getCoeff trms
                                                                        return $ SReal $ mkPolyReal (Right (k, ts))
        cvt x                                                      = return x
        getCoeff (SApp [SCon "*", SNum k, SApp [SCon "^", SCon "x", SNum p]]) = return (k, p)  -- kx^p
        getCoeff (SApp [SCon "*", SNum k,                 SCon "x"        ] ) = return (k, 1)  -- kx
        getCoeff (                        SApp [SCon "^", SCon "x", SNum p] ) = return (1, p)  --  x^p
        getCoeff (                                        SCon "x"          ) = return (1, 1)  --  x
        getCoeff (                SNum k                                    ) = return (k, 0)  -- k
        getCoeff x = die $ "Cannot parse a root-obj,\nProcessing term: " ++ show x
