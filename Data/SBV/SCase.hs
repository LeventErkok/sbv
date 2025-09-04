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

import Data.Char  (isSpace)
import Data.List  (intercalate)
import Data.Maybe (isJust)

-- | What kind of case-match are we given. In each case, the maybe is the possible guard.
data Case = Full    [Pat] Exp (Maybe Exp) -- Fully saturated constructor match: [Pat] -> Body.
          | Partial       Exp (Maybe Exp) -- Wild-card or record match. Exp is the rhs, must be turned
                                          -- into a lambda by expanding with constructors (found later)

-- | Get the guard, if any
getCaseGuard :: Case -> Maybe Exp
getCaseGuard (Full _  _ mbg) = mbg
getCaseGuard (Partial _ mbg) = mbg

-- | Is there a guard?
isGuarded :: Case -> Bool
isGuarded = isJust . getCaseGuard

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
              cases <- mapM matchToPair matches >>= checkCase typ . concat
              buildCase fnName scrut cases
            Right _  -> fail "sCase: internal parse error, not a case-expression"
            Left err -> case lines err of
                           [l, _, e] -> fail $ "sCase parse error [Line " <> l <> "]: " <> e
                           _         -> fail $ "sCase parse error: " <> err

    buildCase caseFunc scrut (Left   cases) = pure $ foldl AppE (caseFunc `AppE` scrut) cases
    buildCase _caseFunc _scrut (Right _chain) = fail $ "Guarded case TBD"

    getGuards :: Body -> [Dec] -> Q [(Exp, Maybe Exp)]
    getGuards (NormalB  rhs)  locals = pure [(addLocals locals rhs, Nothing)]
    getGuards (GuardedB exps) locals = mapM get exps
      where get (NormalG e,  rhs) = pure (addLocals locals rhs, Just e)
            get (PatG stmts, _)   = fail $ unlines $  "sCase: Pattern guards are not supported: "
                                                   : ["        " ++ pprint s | s <- stmts]

    -- Turn where clause into simple let
    addLocals :: [Dec] -> Exp -> Exp
    addLocals [] e = e
    addLocals ds e = LetE ds e

    matchToPair :: Match -> Q [(Maybe (Name, [Pat]), Case)]
    matchToPair (Match pat grhs locals) = do
      rhss <- getGuards grhs locals
      case pat of
        ConP conName _ subpats -> do ps <- traverse patToVar subpats
                                     pure [(Just (conName, ps), Full ps rhs t) | (rhs, t) <- rhss]
        WildP                  ->    pure [(Nothing,            Partial rhs t) | (rhs, t) <- rhss]
        RecP conName []        ->    pure [(Just (conName, []), Partial rhs t) | (rhs, t) <- rhss]
        _ -> fail $ unlines [ "sCase: Unsupported pattern:"
                            , "            Saw: " <> pprint pat
                            , ""
                            , "        Only constructors with variables (i.e., Cstr a b _ d)"
                            , "        Empty record matches (i.e., Cstr{})"
                            , "        And wildcards (i.e., _) for default"
                            , "        are supported."
                            ]

    -- Make sure things are in good-shape and decide if we have guards
    checkCase :: String -> [(Maybe (Name, [Pat]), Case)] -> Q (Either [Exp] [(Maybe Name, Maybe Exp, Exp)])
    checkCase typ cases = do
        cstrsOrig <- getConstructors (mkName typ)

        -- This is a bit dicey as we "trim" the cstr names, but oh well
        let cstrs = [(nameBase c, fts) | (c, fts) <- cstrsOrig]

            shGuard :: Case -> String
            shGuard c = case getCaseGuard c of
                          Nothing -> ""
                          Just e  -> "| " <> pprint e

            shM (Nothing     , g) = "_" <> shGuard g
            shM (Just (c, ps), g) = unwords $ pprint c : map pprint ps ++ [shGuard g]

        -- Step 0: If there's an unguarded wild-card, make sure nothing else follows it:
        let checkWild []                    = pure ()
            checkWild ((Just{}, _)  : rest) = checkWild rest
            checkWild ((Nothing, c) : rest)
              | isGuarded c
              = checkWild rest
              | True
              = case rest of
                  []  -> pure ()
                  red  -> let w | length red > 1 = "matches are"
                                | True           = "match is"
                          in fail $ unlines $ ("sCase: Pattern " ++ w ++ " redundant")
                                            : ["        " ++ shM r | r <- red]
        checkWild cases

        -- Step 2: Make sure every constructor listed actually exists and matches in arity.
        let chk1 :: (Maybe (Name, [Pat]), Case) -> Q ()
            chk1 (Nothing,      _)    = pure ()
            chk1 (Just (n, ps), kind)
              | Just ts <- nameBase n `lookup` cstrs
              = case kind of
                  Full{}    -> unless (length ts == length ps)
                                $ fail $ unlines [ "sCase: Arity mismatch."
                                                 , "        Type       : " ++ typ
                                                 , "        Constructor: " ++ show n
                                                 , "        Expected   : " ++ show (length ts)
                                                 , "        Given      : " ++ show (length ps)
                                                 ]
                  Partial{} -> pure ()
              | True
              = fail $ unlines [ "sCase: Unknown constructor: " <> show n
                               , "        Type          : " ++ typ
                               , "        Saw           : " ++ show n
                               , "        Must be one of: " ++ intercalate ", " (map fst cstrs)
                               ]

        -- Step 2: Make sure constructors that have no guards are not repeated.
        let dups []     = Nothing
            dups (x:xs) | x `elem` xs = Just x
                        | True        = dups xs

            chk2 xs = case dups xs of
                        Nothing -> pure ()
                        Just x  -> fail $ unlines [ "sCase: Duplicate case:"
                                                  , "        Type    : " ++ typ
                                                  , "        Repeated: " ++ show x
                                                  ]

        mapM_ chk1 cases
        chk2 [n | (Just (n, _), c) <- cases, not (isGuarded c)]

        -- At this point, we either have a simple case with no guards, in which case
        -- we translate this to an sCase for that type. So find all alternatives.
        -- Otherwise, this will become an ite-chain
        let hasGuards = any (isGuarded . snd) cases

        if not hasGuards
           then do let -- NB. We don't have to worry about the default having a guard here since we have no guards in this case
                       defaultCase  = Nothing `lookup` cases
                       givens       = [(nameBase c, e) | (Just (c, _), e) <- cases]

                       case2rhs :: Case -> [Type] -> (Maybe Exp, Exp)
                       case2rhs cs ts = (LamE pats <$> mbGuard, LamE pats e)
                         where (mbGuard, e, pats) = case cs of
                                                      Full ps rhs mbt -> (mbt, rhs, ps)
                                                      Partial rhs mbt -> (mbt, rhs, map (const WildP) ts)

                       collect (cstr, ps)
                         | Just e <- cstr `lookup` givens
                         = pure $ case2rhs e ps
                         | True
                         = case defaultCase of
                             Nothing -> fail $ unlines [ "sCase: Pattern match(es) are non-exhaustive."
                                                       , "        Not matched     : " ++ cstr
                                                       , "        Patterns of type: " ++ typ
                                                       , "        Must match each : " ++ intercalate ", " (map fst cstrs)
                                                       , ""
                                                       , "      You can use a '_' to match multiple cases."
                                                       ]
                             Just de -> pure $ case2rhs de ps

                   res <- mapM collect cstrs

                   -- If we reached here, all is well; except we might have an extra wildcard that we did not use
                   when (length cases > length cstrs) $
                     case defaultCase of
                       Nothing -> pure ()
                       Just _  -> fail "sCase: Wildcard match is redundant"

                   -- Double check that we had no guards and return the cases
                   case [r | (Just{}, r) <- res] of
                     [] -> pure $ Left $ map snd res
                     rs -> fail $ unlines $ "sCase: Impossible happened; found a guard in no-guard case."
                                          : [ "        " ++ pprint r | r <- rs]

           else do -- We have guards. For each constructor without a guard, make sure we cover all the cases. If not we complain.
                   let unguardedCases      = [nameBase cstr | (Just (cstr, _), c) <- cases, not (isGuarded c)]
                       hasUnguardedDefault = or [True | (Nothing, c) <- cases, not (isGuarded c)]

                   case filter (`notElem` unguardedCases) (map fst cstrs) of
                     [] | hasUnguardedDefault -> fail "sCase: Wildcard match is redundant"
                     _                        -> pure ()

                   let collect :: (Maybe (Name, [Pat]), Case) -> Q (Maybe Name, Maybe Exp, Exp)

                       -- Wild card match, full constructor application
                       collect (Nothing, Full ps e Nothing)  = pure (Nothing, Nothing,          LamE ps e)
                       collect (Nothing, Full ps e (Just t)) = pure (Nothing, Just (LamE ps t), LamE ps e)

                   res <- mapM collect cases
                   pure $ Right res

    patToVar :: Pat -> Q Pat
    patToVar p@VarP{} = pure p
    patToVar p@WildP  = pure p
    patToVar p        = fail $ "sCase: constructor arguments must be variables, not: " <> pprint p

    parts = go ""
      where go _     ""             = Nothing
            go sofar ('o':'f':rest) = Just (break isSpace (dropWhile isSpace (reverse sofar)), rest)
            go sofar (c:cs)         = go (c:sofar) cs
