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

import Data.Bits           (setBit, testBit)
import Data.Word           (Word32, Word64)
import Data.Char           (isDigit, ord)
import Data.List           (isPrefixOf)
import Data.Maybe          (fromMaybe, listToMaybe)
import Numeric             (readInt, readDec, readHex, fromRat)
import Data.Binary.IEEE754 (wordToFloat, wordToDouble)

import Data.SBV.Core.AlgReals
import Data.SBV.Core.Data (nan, infinity, RoundingMode(..))

-- | ADT S-Expression format, suitable for representing get-model output of SMT-Lib
data SExpr = ECon    String
           | ENum    (Integer, Maybe Int)  -- Second argument is how wide the field was in bits, if known. Useful in FP parsing.
           | EReal   AlgReal
           | EFloat  Float
           | EDouble Double
           | EApp    [SExpr]
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
                              f' <- cvt (EApp f)
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
        pTok "false"              = return $ ENum (0, Nothing)
        pTok "true"               = return $ ENum (1, Nothing)
        pTok ('0':'b':r)          = mkNum (Just (length r))     $ readInt 2 (`elem` "01") (\c -> ord c - ord '0') r
        pTok ('b':'v':r)          = mkNum Nothing               $ readDec (takeWhile (/= '[') r)
        pTok ('#':'b':r)          = mkNum (Just (length r))     $ readInt 2 (`elem` "01") (\c -> ord c - ord '0') r
        pTok ('#':'x':r)          = mkNum (Just (4 * length r)) $ readHex r
        pTok n
          | not (null n) && isDigit (head n)
          = if '.' `elem` n then getReal n
            else mkNum Nothing $ readDec n
        pTok n                 = return $ ECon (constantMap n)
        mkNum l [(n, "")] = return $ ENum (n, l)
        mkNum _ _         = die "cannot read number"
        getReal n = return $ EReal $ mkPolyReal (Left (exact, n'))
          where exact = not ("?" `isPrefixOf` reverse n)
                n' | exact = n
                   | True  = init n
        -- simplify numbers and root-obj values
        cvt (EApp [ECon "to_int",  EReal a])                       = return $ EReal a   -- ignore the "casting"
        cvt (EApp [ECon "to_real", EReal a])                       = return $ EReal a   -- ignore the "casting"
        cvt (EApp [ECon "/", EReal a, EReal b])                    = return $ EReal (a / b)
        cvt (EApp [ECon "/", EReal a, ENum  b])                    = return $ EReal (a                   / fromInteger (fst b))
        cvt (EApp [ECon "/", ENum  a, EReal b])                    = return $ EReal (fromInteger (fst a) /             b      )
        cvt (EApp [ECon "/", ENum  a, ENum  b])                    = return $ EReal (fromInteger (fst a) / fromInteger (fst b))
        cvt (EApp [ECon "-", EReal a])                             = return $ EReal (-a)
        cvt (EApp [ECon "-", ENum a])                              = return $ ENum  (-(fst a), snd a)
        -- bit-vector value as CVC4 prints: (_ bv0 16) for instance
        cvt (EApp [ECon "_", ENum a, ENum _b])                     = return $ ENum a
        cvt (EApp [ECon "root-obj", EApp (ECon "+":trms), ENum k]) = do ts <- mapM getCoeff trms
                                                                        return $ EReal $ mkPolyReal (Right (fst k, ts))
        cvt (EApp [ECon "as", n, EApp [ECon "_", ECon "FloatingPoint", ENum (11, _), ENum (53, _)]]) = getDouble n
        cvt (EApp [ECon "as", n, EApp [ECon "_", ECon "FloatingPoint", ENum ( 8, _), ENum (24, _)]]) = getFloat  n
        cvt (EApp [ECon "as", n, ECon "Float64"])                                                    = getDouble n
        cvt (EApp [ECon "as", n, ECon "Float32"])                                                    = getFloat  n
        -- NB. Note the lengths on the mantissa for the following two are 23/52; not 24/53!
        cvt (EApp [ECon "fp",    ENum (s, Just 1), ENum ( e, Just 8),  ENum (m, Just 23)])           = return $ EFloat  $ getTripleFloat  s e m
        cvt (EApp [ECon "fp",    ENum (s, Just 1), ENum ( e, Just 11), ENum (m, Just 52)])           = return $ EDouble $ getTripleDouble s e m
        cvt (EApp [ECon "_",     ECon "NaN",       ENum ( 8, _),       ENum (24,      _)])           = return $ EFloat  nan
        cvt (EApp [ECon "_",     ECon "NaN",       ENum (11, _),       ENum (53,      _)])           = return $ EDouble nan
        cvt (EApp [ECon "_",     ECon "+oo",       ENum ( 8, _),       ENum (24,      _)])           = return $ EFloat  infinity
        cvt (EApp [ECon "_",     ECon "+oo",       ENum (11, _),       ENum (53,      _)])           = return $ EDouble infinity
        cvt (EApp [ECon "_",     ECon "-oo",       ENum ( 8, _),       ENum (24,      _)])           = return $ EFloat  (-infinity)
        cvt (EApp [ECon "_",     ECon "-oo",       ENum (11, _),       ENum (53,      _)])           = return $ EDouble (-infinity)
        cvt (EApp [ECon "_",     ECon "+zero",     ENum ( 8, _),       ENum (24,      _)])           = return $ EFloat  0
        cvt (EApp [ECon "_",     ECon "+zero",     ENum (11, _),       ENum (53,      _)])           = return $ EDouble 0
        cvt (EApp [ECon "_",     ECon "-zero",     ENum ( 8, _),       ENum (24,      _)])           = return $ EFloat  (-0)
        cvt (EApp [ECon "_",     ECon "-zero",     ENum (11, _),       ENum (53,      _)])           = return $ EDouble (-0)
        cvt x                                                                                        = return x
        getCoeff (EApp [ECon "*", ENum k, EApp [ECon "^", ECon "x", ENum p]]) = return (fst k, fst p)  -- kx^p
        getCoeff (EApp [ECon "*", ENum k,                 ECon "x"        ] ) = return (fst k,     1)  -- kx
        getCoeff (                        EApp [ECon "^", ECon "x", ENum p] ) = return (    1, fst p)  --  x^p
        getCoeff (                                        ECon "x"          ) = return (    1,     1)  --  x
        getCoeff (                ENum k                                    ) = return (fst k,     0)  -- k
        getCoeff x = die $ "Cannot parse a root-obj,\nProcessing term: " ++ show x
        getDouble (ECon s)  = case (s, rdFP (dropWhile (== '+') s)) of
                                ("plusInfinity",  _     ) -> return $ EDouble infinity
                                ("minusInfinity", _     ) -> return $ EDouble (-infinity)
                                ("oo",            _     ) -> return $ EDouble infinity
                                ("-oo",           _     ) -> return $ EDouble (-infinity)
                                ("zero",          _     ) -> return $ EDouble 0
                                ("-zero",         _     ) -> return $ EDouble (-0)
                                ("NaN",           _     ) -> return $ EDouble nan
                                (_,               Just v) -> return $ EDouble v
                                _               -> die $ "Cannot parse a double value from: " ++ s
        getDouble (EApp [_, s, _, _]) = getDouble s
        getDouble (EReal r) = return $ EDouble $ fromRat $ toRational r
        getDouble x         = die $ "Cannot parse a double value from: " ++ show x
        getFloat (ECon s)   = case (s, rdFP (dropWhile (== '+') s)) of
                                ("plusInfinity",  _     ) -> return $ EFloat infinity
                                ("minusInfinity", _     ) -> return $ EFloat (-infinity)
                                ("oo",            _     ) -> return $ EFloat infinity
                                ("-oo",           _     ) -> return $ EFloat (-infinity)
                                ("zero",          _     ) -> return $ EFloat 0
                                ("-zero",         _     ) -> return $ EFloat (-0)
                                ("NaN",           _     ) -> return $ EFloat nan
                                (_,               Just v) -> return $ EFloat v
                                _               -> die $ "Cannot parse a float value from: " ++ s
        getFloat (EReal r)  = return $ EFloat $ fromRat $ toRational r
        getFloat (EApp [_, s, _, _]) = getFloat s
        getFloat x          = die $ "Cannot parse a float value from: " ++ show x

-- | Parses the Z3 floating point formatted numbers like so: 1.321p5/1.2123e9 etc.
rdFP :: (Read a, RealFloat a) => String -> Maybe a
rdFP s = case break (`elem` "pe") s of
           (m, 'p':e) -> rd m >>= \m' -> rd e >>= \e' -> return $ m' * ( 2 ** e')
           (m, 'e':e) -> rd m >>= \m' -> rd e >>= \e' -> return $ m' * (10 ** e')
           (m, "")    -> rd m
           _          -> Nothing
 where rd v = case reads v of
                [(n, "")] -> Just n
                _         -> Nothing

-- | Convert an (s, e, m) triple to a float value
getTripleFloat :: Integer -> Integer -> Integer -> Float
getTripleFloat s e m = wordToFloat w32
  where sign      = [s == 1]
        expt      = [e `testBit` i | i <- [ 7,  6 .. 0]]
        mantissa  = [m `testBit` i | i <- [22, 21 .. 0]]
        positions = [i | (i, b) <- zip [31, 30 .. 0] (sign ++ expt ++ mantissa), b]
        w32       = foldr (flip setBit) (0::Word32) positions

-- | Convert an (s, e, m) triple to a float value
getTripleDouble :: Integer -> Integer -> Integer -> Double
getTripleDouble s e m = wordToDouble w64
  where sign      = [s == 1]
        expt      = [e `testBit` i | i <- [10,  9 .. 0]]
        mantissa  = [m `testBit` i | i <- [51, 50 .. 0]]
        positions = [i | (i, b) <- zip [63, 62 .. 0] (sign ++ expt ++ mantissa), b]
        w64       = foldr (flip setBit) (0::Word64) positions

-- | Special constants of SMTLib2 and their internal translation. Mainly
-- rounding modes for now.
constantMap :: String -> String
constantMap n = fromMaybe n (listToMaybe [to | (from, to) <- special, n `elem` from])
 where special = [ (["RNE", "roundNearestTiesToEven"], show RoundNearestTiesToEven)
                 , (["RNA", "roundNearestTiesToAway"], show RoundNearestTiesToAway)
                 , (["RTP", "roundTowardPositive"],    show RoundTowardPositive)
                 , (["RTN", "roundTowardNegative"],    show RoundTowardNegative)
                 , (["RTZ", "roundTowardZero"],        show RoundTowardZero)
                 ]
