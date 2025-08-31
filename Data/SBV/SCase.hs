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

import Data.SBV.Client (getConstructors)

import Data.Char (isSpace)

-- | Quasi-quoter for symbolic case expressions.
sCase :: QuasiQuoter
sCase = QuasiQuoter
  { quoteExp  = extract
  , quotePat  = bad "pattern"
  , quoteType = bad "type"
  , quoteDec  = bad "declaration"
  }
  where
    bad ctx _ = fail $ "sCase: not usable in " <> ctx <> " context"

    extract :: String -> ExpQ
    extract src =
      case parts src of
        Nothing -> fail "sCase: expected syntax: func expr of ..."
        Just ((typ, scrutStr), altsStr) -> do
          let fnTok    = "sCase" <> typ
              fullCase = "case " <> scrutStr <> " of " <> altsStr
          case Meta.parseExp fullCase of
            Right (CaseE scrut matches) -> do
              fnName <- lookupValueName fnTok >>= \case
                Just n  -> pure (VarE n)
                Nothing -> fail $ "sCase: unknown function " <> fnTok
              validateWildcards matches
              cases <- mapM matchToPair matches >>= orient typ
              pure $ foldl AppE (fnName `AppE` scrut) cases
            Right _  -> fail "sCase: internal parse error, not a case-expression"
            Left err -> fail ("sCase parse error:\n" <> err <> "\nwhile parsing:\n" <> fullCase)

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
        _ -> fail $ "sCase: only constructor patterns with variables, or _ for default, are supported. Saw: " <> show pat
    matchToPair _ =
      fail "sCase: only simple matches with normal RHS are supported"

    -- Orient makes sure things are in good shape..
    orient :: String -> [(Maybe (Name, Int), Exp)] -> Q [Exp]
    orient typ cases = do _cstrs <- getConstructors (mkName typ)
                          -- _ <- error (show (cstrs, cases))
                          pure $ map snd cases

    patToVar :: Pat -> Q Pat
    patToVar p@VarP{} = pure p
    patToVar p@WildP  = pure p
    patToVar p        = fail $ "sCase: constructor arguments must be variables, not: " <> show p

    parts = go ""
      where go _     ""             = Nothing
            go sofar ('o':'f':rest) = Just (break isSpace (dropWhile isSpace (reverse sofar)), rest)
            go sofar (c:cs)         = go (c:sofar) cs

    -- Ensure at most one wildcard, and if present, only at the end
    validateWildcards :: [Match] -> Q ()
    validateWildcards ms = do
      let (wilds, _nonWilds) = partitionWild ms
      case wilds of
        [] -> pure ()
        [lastM] | lastM == last ms -> pure ()
        [badM] -> fail $ "sCase: wildcard (_) must be the last alternative. Found earlier: " <> show badM
        _ -> fail "sCase: at most one wildcard (_) allowed"

    partitionWild :: [Match] -> ([Match],[Match])
    partitionWild = foldr go ([],[])
      where
        go m (ws, ns) =
          case m of
            Match WildP _ _ -> (m:ws, ns)
            _               -> (ws, m:ns)
