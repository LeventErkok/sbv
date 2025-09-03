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

import Control.Monad (unless, when)

import Data.SBV.Client (getConstructors)

import Data.Char (isSpace)
import Data.List (intercalate)

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
              cases <- mapM matchToPair matches >>= orient typ
              pure $ foldl AppE (fnName `AppE` scrut) cases
            Right _  -> fail "sCase: internal parse error, not a case-expression"
            Left err -> case lines err of
                           [l, _, e] -> fail $ "sCase parse error [Line " <> l <> "]: " <> e
                           _         -> fail $ "sCase parse error: " <> err

    matchToPair :: Match -> Q (Maybe (Name, [Pat]), Exp)
    matchToPair (Match pat (NormalB rhs) []) =
      case pat of
        ConP conName _ subpats -> do
          ps <- traverse patToVar subpats
          let lam = LamE ps rhs
          pure (Just (conName, ps), lam)
        WildP -> do
          let lam = LamE [] rhs
          pure (Nothing, lam)
        _ -> fail $ "sCase: only constructor patterns with variables, or _ for default, are supported. Saw: " <> pprint pat
    matchToPair _ =
      fail "sCase: only simple matches with normal RHS are supported"

    -- Orient makes sure things are in good shape..
    orient :: String -> [(Maybe (Name, [Pat]), Exp)] -> Q [Exp]
    orient typ cases = do cstrsOrig <- getConstructors (mkName typ)

                          -- This is a bit dicey as we "trim" the cstr names, but oh well
                          let cstrs = [(nameBase c, fts) | (c, fts) <- cstrsOrig]

                              shM Nothing        = "_"
                              shM (Just (c, ps)) = unwords $ pprint c : map pprint ps

                          -- Step 0: If there's a wild-card, make sure nothing else follows it:
                          let checkWild []                    = pure ()
                              checkWild ((Just{}, _)  : rest) = checkWild rest
                              checkWild ((Nothing, _) : rest) = case map fst rest of
                                                                 []  -> pure ()
                                                                 red  -> let w | length red > 1 = "matches are"
                                                                               | True           = "match is"
                                                                         in fail $ unlines $  ["sCase: Pattern " ++ w ++ " redundant"]
                                                                                           ++ ["        " ++ shM r | r <- red]
                          checkWild cases

                          -- Step 2: Make sure every constructor listed actually exists and
                          -- matches in arity.
                          let chk1 (Nothing,      _) = pure ()
                              chk1 (Just (n, ps), _)
                                | Just ts <- nameBase n `lookup` cstrs
                                = unless (length ts == length ps)
                                       $ fail $ unlines [ "sCase: Arity mismatch."
                                                        , "        Type       : " ++ typ
                                                        , "        Constructor: " ++ show n
                                                        , "        Expected   : " ++ show (length ts)
                                                        , "        Given      : " ++ show (length ps)
                                                        ]
                                | True
                                = fail $ unlines [ "sCase: Unknown constructor: " <> show n
                                                 , "        Type          : " ++ typ
                                                 , "        Saw           : " ++ show n
                                                 , "        Must be one of: " ++ intercalate ", " (map fst cstrs)
                                                 ]

                          -- Step 2: Make sure constructors are not repeated
                          let dups []     = Nothing
                              dups (x:xs) | x `elem` xs = Just x
                                          | True        = dups xs

                              chk2 xs = case dups xs of
                                          Nothing -> pure ()
                                          Just x  -> fail $ unlines [ "sCase: Duplicate case:"
                                                                    , "Type    : " ++ typ
                                                                    , "Repeated: " ++ show x
                                                                    ]

                          mapM_ chk1 cases
                          chk2 [n | (Just (n, _), _) <- cases]

                          -- Find the case for each constructor. If one is not found use the default.
                          -- If there's no default, complain.
                          let defaultCase  = Nothing `lookup` cases
                              givens       = [(nameBase c, e) | (Just (c, _), e) <- cases]

                              collect (cstr, ps)
                                | Just e <- cstr `lookup` givens 
                                =  pure e
                                | True
                                = case defaultCase of
                                    Nothing -> fail $ unlines [ "sCase: Pattern match(es) are non-exhaustive."
                                                              , "        Not matched     : " ++ cstr
                                                              , "        Patterns of type: " ++ typ
                                                              , "        Must match each : " ++ intercalate ", " (map fst cstrs)
                                                              , ""
                                                              , "      You can use a '_' to match multiple cases."
                                                              ]
                                    Just de -> pure $ LamE (map (const WildP) ps) de

                          res <- mapM collect cstrs

                          -- If we reached here, all is well; except we might have an extra wildcard that we did not use
                          when (length cases > length cstrs) $
                            case defaultCase of
                              Nothing -> pure ()
                              Just _  -> fail "sCase: Wildcard match is redundant"

                          pure res

    patToVar :: Pat -> Q Pat
    patToVar p@VarP{} = pure p
    patToVar p@WildP  = pure p
    patToVar p        = fail $ "sCase: constructor arguments must be variables, not: " <> pprint p

    parts = go ""
      where go _     ""             = Nothing
            go sofar ('o':'f':rest) = Just (break isSpace (dropWhile isSpace (reverse sofar)), rest)
            go sofar (c:cs)         = go (c:sofar) cs
