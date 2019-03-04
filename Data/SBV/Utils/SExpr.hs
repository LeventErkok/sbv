-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Utils.SExpr
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Parsing of S-expressions (mainly used for parsing SMT-Lib get-value output)
-----------------------------------------------------------------------------

{-# LANGUAGE BangPatterns #-}

module Data.SBV.Utils.SExpr (SExpr(..), parenDeficit, parseSExpr, parseSExprFunction) where

import Data.Bits   (setBit, testBit)
import Data.Char   (isDigit, ord, isSpace)
import Data.Either (partitionEithers)
import Data.List   (isPrefixOf)
import Data.Maybe  (fromMaybe, listToMaybe)
import Data.Word   (Word32, Word64)

import Numeric    (readInt, readDec, readHex, fromRat)

import Data.SBV.Core.AlgReals
import Data.SBV.Core.Data (nan, infinity, RoundingMode(..))

import Data.SBV.Utils.Numeric (fpIsEqualObjectH)

import Data.Numbers.CrackNum (wordToFloat, wordToDouble)

-- | ADT S-Expression format, suitable for representing get-model output of SMT-Lib
data SExpr = ECon    String
           | ENum    (Integer, Maybe Int)  -- Second argument is how wide the field was in bits, if known. Useful in FP parsing.
           | EReal   AlgReal
           | EFloat  Float
           | EDouble Double
           | EApp    [SExpr]
           deriving Show

-- | Extremely simple minded tokenizer, good for our use model.
tokenize :: String -> [String]
tokenize inp = go inp []
 where go "" sofar = reverse sofar

       go (c:cs) sofar
          | isSpace c = go (dropWhile isSpace cs) sofar

       go ('(':cs) sofar = go cs ("(" : sofar)
       go (')':cs) sofar = go cs (")" : sofar)

       go (':':':':cs) sofar = go cs ("::" : sofar)

       go (':':cs) sofar = case break (`elem` stopper) cs of
                            (pre, rest) -> go rest ((':':pre) : sofar)

       go ('|':r) sofar = case span (/= '|') r of
                            (pre, '|':rest) -> go rest (pre : sofar)
                            (pre, rest)     -> go rest (pre : sofar)

       go ('"':r) sofar = go rest (finalStr : sofar)
           where grabString []             acc = (reverse acc, [])         -- Strictly speaking, this is the unterminated string case; but let's ignore
                 grabString ('"' :'"':cs)  acc = grabString cs ('"' :acc)
                 grabString ('"':cs)       acc = (reverse acc, cs)
                 grabString (c:cs)         acc = grabString cs (c:acc)

                 (str, rest) = grabString r []
                 finalStr    = '"' : str ++ "\""

       go cs sofar = case span (`notElem` stopper) cs of
                       (pre, post) -> go post (pre : sofar)

       -- characters that can stop the current token
       -- it is *crucial* that this list contains every character
       -- we can match in one of the previous cases!
       stopper = " \t\n():|\""

-- | The balance of parens in this string. If 0, this means it's a legit line!
parenDeficit :: String -> Int
parenDeficit = go 0 . tokenize
  where go :: Int -> [String] -> Int
        go !balance []           = balance
        go !balance ("(" : rest) = go (balance+1) rest
        go !balance (")" : rest) = go (balance-1) rest
        go !balance (_   : rest) = go balance     rest

-- | Parse a string into an SExpr, potentially failing with an error message
parseSExpr :: String -> Either String SExpr
parseSExpr inp = do (sexp, extras) <- parse inpToks
                    if null extras
                       then case sexp of
                              EApp [ECon "error", ECon er] -> Left $ "Solver returned an error: " ++ er
                              _                            -> return sexp

                       else die "Extra tokens after valid input"
  where inpToks = tokenize inp

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

        pTok "false" = return $ ENum (0, Nothing)
        pTok "true"  = return $ ENum (1, Nothing)

        pTok ('0':'b':r)                                 = mkNum (Just (length r))     $ readInt 2 (`elem` "01") (\c -> ord c - ord '0') r
        pTok ('b':'v':r) | not (null r) && all isDigit r = mkNum Nothing               $ readDec (takeWhile (/= '[') r)
        pTok ('#':'b':r)                                 = mkNum (Just (length r))     $ readInt 2 (`elem` "01") (\c -> ord c - ord '0') r
        pTok ('#':'x':r)                                 = mkNum (Just (4 * length r)) $ readHex r

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

-- | Parse a function like value. These come in two flavors: Either in the form of
-- a store-expression or a lambda-expression. So we handle both here.
parseSExprFunction :: SExpr -> Maybe (Either String ([([SExpr], SExpr)], SExpr))
parseSExprFunction e
  | Just r <- parseLambdaExpression  e = Just (Right r)
  | Just r <- parseStoreAssociations e = Just r
  | True                               = Nothing         -- out-of luck. NB. This is where we would add support for other solvers!

-- | Parse a lambda expression, most likely z3 specific. There's some guess work
-- involved here regarding how z3 produces lambda-expressions; while we try to
-- be flexible, this is certainly not a full fledged parser. But hopefully it'll
-- cover everything z3 will throw at it.
parseLambdaExpression :: SExpr -> Maybe ([([SExpr], SExpr)], SExpr)
parseLambdaExpression funExpr = case funExpr of
                                  EApp [ECon "lambda", EApp params, body] -> mapM getParam params >>= flip lambda body >>= chainAssigns
                                  _                                       -> Nothing
  where getParam (EApp [ECon v, _]) = Just v
        getParam _                  = Nothing

        lambda :: [String] -> SExpr -> Maybe [Either ([SExpr], SExpr) SExpr]
        lambda params body = reverse <$> go [] body
          where true  = ENum (1, Nothing)
                false = ENum (0, Nothing)

                go :: [Either ([SExpr], SExpr) SExpr] -> SExpr -> Maybe [Either ([SExpr], SExpr) SExpr]
                go sofar (EApp [ECon "ite", selector, thenBranch, elseBranch])
                  = do s  <- select selector
                       tB <- go [] thenBranch
                       case cond s tB of
                          Just sv -> go (Left sv : sofar) elseBranch
                          _       -> Nothing

                -- z3 sometimes puts together a bunch of booleans as final expression,
                -- see if we can catch that.
                go sofar e
                 | Just s <- select e
                 = go (Left (s, true) : sofar) false

                -- Otherwise, just treat it as an "unknown" arbitrary expression
                -- as the default. It could be something arbitrary of course, but it's
                -- too complicated to parse; and hopefully this is good enogh.
                go sofar e = Just $ Right e : sofar

                cond :: [SExpr] -> [Either ([SExpr], SExpr) SExpr] -> Maybe ([SExpr], SExpr)
                cond s [Right v] = Just (s, v)
                cond _ _         = Nothing

                -- select takes the condition of an ite, and returns precisely what match is done to the parameters
                select :: SExpr -> Maybe [SExpr]
                select e
                   | Just dict <- build e [] = mapM (`lookup` dict) params
                   | True                    = Nothing
                  where -- build a dictionary of assignments from the scrutinee
                        build :: SExpr -> [(String, SExpr)] -> Maybe [(String, SExpr)]
                        build (EApp (ECon "and" : rest)) sofar = let next _ Nothing  = Nothing
                                                                     next c (Just x) = build c x
                                                                 in foldr next (Just sofar) rest

                        build expr sofar | Just (v, r) <- grok expr, v `elem` params = Just $ (v, r) : sofar
                                         | True                                      = Nothing

                        -- See if we can figure out what z3 is telling us; hopefully this
                        -- mapping covers everything we can see:
                        grok (EApp [ECon "=", ECon v, r]) = Just (v, r)
                        grok (EApp [ECon "=", r, ECon v]) = Just (v, r)
                        grok (EApp [ECon "not", ECon v])  = Just (v, false) -- boolean negation, require it to be false
                        grok (ECon v)                     = Just (v, true)  -- boolean identity, require it to be true

                        -- Tough luck, we couldn't understand:
                        grok _ = Nothing

-- | Parse a series of associations in the array notation, things that look like:
--
--     (store (store ((as const Array) 12) 3 5 9) 5 6 75)
--
-- This is (most likely) entirely Z3 specific. So, we might have to tweak it for other
-- solvers; though it isn't entirely clear how to do that as we do not know what solver
-- we're using here. The trick is to handle all of possible SExpr's we see.
-- We'll cross that bridge when we get to it.
--
-- NB. In case there's no "constraint" on the UI, Z3 produces the self-referential model:
--
--    (x (_ as-array x))
--
-- So, we specifically handle that here, by returning a Left of that name.
parseStoreAssociations :: SExpr -> Maybe (Either String ([([SExpr], SExpr)], SExpr))
parseStoreAssociations (EApp [ECon "_", ECon "as-array", ECon nm]) = Just $ Left nm
parseStoreAssociations e                                           = Right <$> (chainAssigns =<< vals e)
    where vals :: SExpr -> Maybe [Either ([SExpr], SExpr) SExpr]
          vals (EApp [EApp [ECon "as", ECon "const", ECon "Array"],            defVal]) = return [Right defVal]
          vals (EApp [EApp [ECon "as", ECon "const", EApp (ECon "Array" : _)], defVal]) = return [Right defVal]
          vals (EApp (ECon "store" : prev : argsVal)) | length argsVal >= 2             = do rest <- vals prev
                                                                                             return $ Left (init argsVal, last argsVal) : rest
          vals _                                                                        = Nothing

-- | Turn a sequence of left-right chain assignments (condition + free) into a single chain
chainAssigns :: [Either ([SExpr], SExpr) SExpr] -> Maybe ([([SExpr], SExpr)], SExpr)
chainAssigns chain = regroup $ partitionEithers chain
  where regroup (vs, [d]) = Just (checkDup vs, d)
        regroup _         = Nothing

        -- If we get into a case like this:
        --
        --     (store (store a 1 2) 1 3)
        --
        -- then we need to drop the 1->2 assignment!
        --
        -- The way we parse these, the first assignment wins.
        checkDup :: [([SExpr], SExpr)] -> [([SExpr], SExpr)]
        checkDup []              = []
        checkDup (a@(key, _):as) = a : checkDup [r | r@(key', _) <- as, not (key `sameKey` key')]

        sameKey :: [SExpr] -> [SExpr] -> Bool
        sameKey as bs
          | length as == length bs = and $ zipWith same as bs
          | True                   = error $ "Data.SBV: Differing length of key received in chainAssigns: " ++ show (as, bs)

        -- We don't want to derive Eq; as this is more careful on floats and such
        same :: SExpr -> SExpr -> Bool
        same x y = case (x, y) of
                     (ECon a,      ECon b)       -> a == b
                     (ENum (i, _), ENum (j, _))  -> i == j
                     (EReal a,     EReal b)      -> algRealStructuralEqual a b
                     (EFloat  f1,  EFloat  f2)   -> fpIsEqualObjectH f1 f2
                     (EDouble d1,  EDouble d2)   -> fpIsEqualObjectH d1 d2
                     (EApp as,     EApp bs)      -> length as == length bs && and (zipWith same as bs)
                     (e1,          e2)           -> if eRank e1 == eRank e2
                                                    then error $ "Data.SBV: You've found a bug in SBV! Please report: SExpr(same): " ++ show (e1, e2)
                                                    else False
        -- Defensive programming: It's too long to list all pair up, so we use this function and
        -- GHC's pattern-match completion warning to catch cases we might've forgotten. If
        -- you ever get the error line above fire, because you must've disabled the pattern-match
        -- completion check warning! Shame on you.
        eRank :: SExpr -> Int
        eRank ECon{}    = 0
        eRank ENum{}    = 1
        eRank EReal{}   = 2
        eRank EFloat{}  = 3
        eRank EDouble{} = 4
        eRank EApp{}    = 5

{-# ANN chainAssigns ("HLint: ignore Redundant if" :: String) #-}
