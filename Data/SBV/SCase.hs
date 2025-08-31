-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.SCase
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Add support for symbolic case expressions. Constructed with the help of ChatGPT,
-- which was remarkably good at giving me the basic structure.
--
-- Provides a quasiquoter  `[sCase|Expr expr of ... |]` for symbolic cases
-- where 'Expr' is the underlying type.
-----------------------------------------------------------------------------

{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.SCase (sCase) where

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import qualified Language.Haskell.Meta.Parse as Meta

import Control.Monad (unless)

import Data.SBV.Client (getConstructors)

import Data.Char (isSpace)
import Data.List (intercalate)

-- | Utility: add filename and line number to an error
errorWithLoc :: String -> Q a
errorWithLoc msg = do loc <- location
                      fail $ intercalate "\n" $ ("Data.SBV.sCase: error at " ++ formatLoc loc)
                                              : zipWith tab (True : repeat False) (lines msg)
  where formatLoc :: Loc -> String
        formatLoc loc = loc_filename loc ++ ":" ++ show line ++ ":" ++ show col
          where (line, col) = loc_start loc

        tab False = ("          " ++)
        tab True  = ("        " ++)

-- | Quasi-quoter for symbolic case expressions.
sCase :: QuasiQuoter
sCase = QuasiQuoter
  { quoteExp  = extract
  , quotePat  = bad "pattern"
  , quoteType = bad "type"
  , quoteDec  = bad "declaration"
  }
  where
    bad ctx _ = errorWithLoc $ "sCase: not usable in " <> ctx <> " context"

    extract :: String -> ExpQ
    extract src =
      case parts src of
        Nothing -> errorWithLoc "sCase: expected syntax: func expr of ..."
        Just ((typ, scrutStr), altsStr) -> do
          let fnTok    = "sCase" <> typ
              fullCase = "case " <> scrutStr <> " of " <> altsStr
          case Meta.parseExp fullCase of
            Right (CaseE scrut matches) -> do
              fnName <- lookupValueName fnTok >>= \case
                Just n  -> pure (VarE n)
                Nothing -> errorWithLoc $ "sCase: unknown function " <> fnTok
              validateWildcards matches
              cases <- mapM matchToPair matches >>= orient typ
              pure $ foldl AppE (fnName `AppE` scrut) cases
            Right _  -> errorWithLoc "sCase: internal parse error, not a case-expression"
            Left err -> errorWithLoc ("sCase parse error:\n" <> err <> "\nwhile parsing:\n" <> fullCase)

    matchToPair :: Match -> Q (Maybe (Name, Int), Exp)
    matchToPair (Match pat (NormalB rhs) []) =
      case pat of
        ConP conName _ subpats -> do
          ps <- traverse patToVar subpats
          let lam = LamE ps rhs
          pure (Just (conName, length ps), lam)
        WildP -> do
          let lam = LamE [] rhs
          pure (Nothing, lam)
        _ -> errorWithLoc $ "sCase: only constructor patterns with variables, or _ for default, are supported. Saw: " <> pprint pat
    matchToPair _ =
      errorWithLoc "sCase: only simple matches with normal RHS are supported"

    -- Orient makes sure things are in good shape..
    orient :: String -> [(Maybe (Name, Int), Exp)] -> Q [Exp]
    orient typ cases = do cstrsOrig <- getConstructors (mkName typ)

                          -- This is a bit dicey as we "trim" the cstr names, but oh well
                          let cstrs = [(nameBase c, fts) | (c, fts) <- cstrsOrig]

                          -- Step 0: Make sure there's at most one wild-card and it appears at the end
                          -- This is done during parsing, so no need to do it again

                          -- Step 1: Make sure every constructor listed actually exists and
                          -- matches in arity.
                          let chk1 (Nothing,     _) = pure ()
                              chk1 (Just (n, a), _)
                                | Just ts <- nameBase n `lookup` cstrs
                                = unless (length ts == a)
                                       $ errorWithLoc $ unlines ["sCase: Arity mismatch."
                                                                , "Type       : " ++ typ
                                                                , "Constructor: " ++ show n
                                                                , "Expected   : " ++ show (length ts)
                                                                , "Given      : " ++ show a
                                                                ]
                                | True
                                = errorWithLoc $ unlines [ "sCase: Unknown constructor: " <> show n
                                                         , "Type          : " ++ typ
                                                         , "Saw           : " ++ show n
                                                         , "Must be one of: " ++ intercalate ", " (map fst cstrs)
                                                         ]

                          -- Step 2: Make sure constructors are not repeated
                          let dups []     = Nothing
                              dups (x:xs) | x `elem` xs = Just x
                                          | True        = dups xs

                              chk2 xs = case dups xs of
                                          Nothing -> pure ()
                                          Just x  -> errorWithLoc $ unlines [ "sCase: Duplicate case:"
                                                                            , "Type    : " ++ typ
                                                                            , "Repeated: " ++ show x
                                                                            ]

                          mapM_ chk1 cases
                          chk2 [n | (Just (n, _), _) <- cases]

                          -- Step 3: Do we have any missing cases? Substitute defaults for them
                          -- based on the wildcard match given. If not complain.
                          -- TODO

                          -- Step 4: Order them
                          -- TODO
                          pure $ map snd cases

    patToVar :: Pat -> Q Pat
    patToVar p@VarP{} = pure p
    patToVar p@WildP  = pure p
    patToVar p        = errorWithLoc $ "sCase: constructor arguments must be variables, not: " <> pprint p

    parts = go ""
      where go _     ""             = Nothing
            go sofar ('o':'f':rest) = Just (break isSpace (dropWhile isSpace (reverse sofar)), rest)
            go sofar (c:cs)         = go (c:sofar) cs

    -- Ensure at most one wildcard, and if present, only at the end
    validateWildcards :: [Match] -> Q ()
    validateWildcards ms = do
      let (wilds, _nonWilds) = partitionWild ms
      case wilds of
        []                         -> pure ()
        [lastM] | lastM == last ms -> pure ()
        [badM]                      -> errorWithLoc $ "sCase: wildcard (_) must be the last alternative. Found earlier: " <> pprint badM
        _                           -> errorWithLoc "sCase: at most one wildcard (_) allowed"

    partitionWild :: [Match] -> ([Match],[Match])
    partitionWild = foldr go ([],[])
      where
        go m (ws, ns) =
          case m of
            Match WildP _ _ -> (m:ws, ns)
            _               -> (ws, m:ns)
