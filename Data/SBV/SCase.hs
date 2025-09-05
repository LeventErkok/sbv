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

-- | What kind of case-match are we given. In each case, the last maybe exp is the possible guard.
data Case = CMatch Name (Maybe [Pat]) Exp (Maybe Exp) -- Cstr a b _ c d if maybe, Cstr{} if nothing on pats
          | CWild                     Exp (Maybe Exp) -- wild-card: _

-- | Show a case nicely
showCase :: Case -> String
showCase sc = case sc of
                CMatch c (Just ps) _ mbG -> unwords $ pprint c : map pprint ps ++ shGuard mbG
                CMatch c Nothing   _ mbG -> unwords $ pprint c : "{}"           : shGuard mbG
                CWild              _ mbG -> unwords $ "_"                       : shGuard mbG
 where shGuard Nothing  = []
       shGuard (Just e) = ["|", pprint e]


-- | Get the name of the constructor, if any
getCaseConstructor :: Case -> Maybe Name
getCaseConstructor (CMatch nm _ _ _) = Just nm
getCaseConstructor (CWild       _ _) = Nothing

-- | Get the guard, if any
getCaseGuard :: Case -> Maybe Exp
getCaseGuard (CMatch _ _ _ mbg) = mbg
getCaseGuard (CWild      _ mbg) = mbg

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

    matchToPair :: Match -> Q [Case]
    matchToPair (Match pat grhs locals) = do
      rhss <- getGuards grhs locals
      case pat of
        ConP conName _ subpats -> do ps <- traverse patToVar subpats
                                     pure [CMatch conName (Just ps) rhs t | (rhs, t) <- rhss]
        RecP conName []        ->    pure [CMatch conName Nothing   rhs t | (rhs, t) <- rhss]
        WildP                  ->    pure [CWild                    rhs t | (rhs, t) <- rhss]
        _ -> fail $ unlines [ "sCase: Unsupported pattern:"
                            , "            Saw: " <> pprint pat
                            , ""
                            , "        Only constructors with variables (i.e., Cstr a b _ d)"
                            , "        Empty record matches (i.e., Cstr{})"
                            , "        And wildcards (i.e., _) for default"
                            , "        are supported."
                            ]

    -- Make sure things are in good-shape and decide if we have guards
    checkCase :: String -> [Case] -> Q (Either [Exp] [(Maybe Name, Maybe Exp, Exp)])
    checkCase typ cases = do
        cstrs <- getConstructors (mkName typ)

        -- Is there a catch all clause?
        let hasCatchAll = or [True | CWild _ Nothing <- cases]

        -- Step 0: If there's an unguarded wild-card, make sure nothing else follows it.
        -- Note that this also handles wild-card being present twice.
        let checkWild []                       = pure ()
            checkWild (CMatch{}        : rest) = checkWild rest
            checkWild (CWild _ Just{}  : rest) = checkWild rest
            checkWild (CWild _ Nothing : rest) = case rest of
                                                  []  -> pure ()
                                                  red  -> let w | length red > 1 = "matches are"
                                                                | True           = "match is"
                                                          in fail $ unlines $ ("sCase: Pattern " ++ w ++ " redundant")
                                                                            : ["        " ++ showCase r | r <- red]
        checkWild cases

        -- Step 2: Make sure every constructor listed actually exists and matches in arity.
        let chk1 :: Case -> Q ()
            chk1 c = case c of
                       CMatch nm ps _ _ -> isSafe nm (length <$> ps)
                       CWild        _ _ -> pure ()
              where isSafe :: Name -> Maybe Int -> Q ()
                    isSafe nm mbLen
                      | Just ts <- nameBase nm `lookup` [(nameBase cnm, t) | (cnm, t) <- cstrs]
                      = case mbLen of
                           Nothing  -> pure ()
                           Just cnt -> unless (length ts == cnt)
                                            $ fail $ unlines [ "sCase: Arity mismatch."
                                                             , "        Type       : " ++ typ
                                                             , "        Constructor: " ++ nameBase nm
                                                             , "        Expected   : " ++ show (length ts)
                                                             , "        Given      : " ++ show cnt
                                                             ]
                      | True
                      = fail $ unlines [ "sCase: Unknown constructor:"
                                       , "        Type          : " ++ typ
                                       , "        Saw           : " ++ nameBase nm
                                       , "        Must be one of: " ++ intercalate ", " (map (nameBase . fst) cstrs)
                                       ]

        mapM_ chk1 cases

        -- Step 2: Make sure constructors matches are not overlapping
        let overlap x   = fail $ unlines [ "sCase: Overlapping case constructors:"
                                         , "        Type       : " ++ typ
                                         , "        Constructor: " ++ showCase x
                                         ]

            unmatched x = fail $ unlines [ "sCase: Non-exhaustive match:"
                                         , "        Type       : " ++ typ
                                         , "        Constructor: " ++ showCase x
                                         ]

            nonExhaustive cstr =  fail $ unlines [ "sCase: Pattern match(es) are non-exhaustive."
                                                 , "        Not matched     : " ++ nameBase cstr
                                                 , "        Patterns of type: " ++ typ
                                                 , "        Must match each : " ++ intercalate ", " (map (nameBase . fst) cstrs)
                                                 , ""
                                                 , "      You can use a '_' to match multiple cases."
                                                 ]
            -- We're done
            chk2 [] = pure ()

            -- If we have a guarded match, then this guard can fail. So either there must be a match
            -- for it later on, or there must be a catch-all. Note that if it exists later, we don't
            -- care if that occurrence is guarded or not; because if it is guarded, we'll fail on the last one.
            chk2 (c@(CMatch nm _ _ (Just {})) : rest)
              | hasCatchAll || Just nm `elem` map getCaseConstructor rest
              = chk2 rest
              | True
              = unmatched c

            -- If we have a non-guarded match, then there must be no matches for this constructor later on
            chk2 (c@(CMatch nm _ _ Nothing) : rest)
              | Just nm `elem` map getCaseConstructor rest
              = overlap c
              | True
              = chk2 rest

            -- If there's a guarded wildcard, must make sure there's a catch all afterwards
            chk2 (c@(CWild _ Just{}) : rest)
              | hasCatchAll
              = chk2 rest
              | True
              = unmatched c

            -- No need to worry about anything following catch-all, since we already covered that before
            chk2 (CWild _ Nothing : rest) = chk2 rest

        chk2 cases

        -- At this point, we either have a simple case with no guards, in which case
        -- we translate this to an sCase for that type. So find all alternatives.
        -- Otherwise, this will become an ite-chain
        let hasGuards = any isGuarded cases

        if not hasGuards
           then do let defaultCase  = case [((e, mbg), c) | c@(CWild e mbg) <- cases] of
                                        []                  -> Nothing
                                        [((e, Nothing), _)] -> Just e
                                        cs -> fail $ unlines $   "sCase: Impossible happened; found unexpected cases:"
                                                             :  [ "        " ++ showCase c | c <- map snd cs]
                                                             ++ [ ""
                                                                , "      Please report this as a bug."
                                                                ]
                       find _ []     = Nothing
                       find w (c:cs)
                         | matches = Just c
                         | True    = find w cs
                         where matches = case c of
                                           CMatch nm _ _ _ -> nameBase nm == nameBase w
                                           CWild       _ _ -> False

                       case2rhs :: Case -> [Type] -> (Maybe Exp, Exp)
                       case2rhs cs ts = (LamE pats <$> mbGuard, LamE pats e)
                         where (mbGuard, e, pats) = case cs of
                                                      CMatch  _ (Just ps) rhs mbt -> (mbt, rhs, ps)
                                                      CMatch  _ Nothing   rhs mbt -> (mbt, rhs, map (const WildP) ts)
                                                      CWild               rhs mbt -> (mbt, rhs, map (const WildP) ts)

                       collect (cstr, ts)
                         | Just e <- find cstr cases
                         = pure $ case2rhs e ts
                         | True
                         = case defaultCase of
                             Nothing -> nonExhaustive cstr
                             Just de -> do let ps = map (const WildP) ts
                                           pure (Nothing, LamE ps de)

                   res <- mapM collect cstrs

                   -- If we reached here, all is well; except we might have an extra wildcard that we did not use
                   when (length cases > length cstrs) $
                     case defaultCase of
                       Nothing -> pure ()
                       Just _  -> fail "sCase: Wildcard match is redundant"

                   -- Double check that we had no guards and return the cases
                   case [r | (Just{}, r) <- res] of
                     [] -> pure $ Left $ map snd res
                     rs -> fail $ unlines $    "sCase: Impossible happened; found a guard in no-guard case."
                                          :  [ "        " ++ pprint r | r <- rs]
                                          ++ [ ""
                                             , "      Please report this as a bug."
                                             ]

           else do -- We have guards.

                   -- Collect, for each constructor, the corresponding cases:
                   let cstrMatches :: [(Name, ([Type], [Case]))]
                       cstrMatches = map (\(cstr, ts) -> (cstr, (ts, concatMap (matches cstr) cases))) cstrs
                         where matches cstr c | Just n <- getCaseConstructor c, nameBase n == nameBase cstr = [c]
                                              | True                                                        = []

                   -- Make sure we have a match for every constructor or a catch-all
                   unless hasCatchAll $ case [nm | (nm, (_, [])) <- cstrMatches] of
                                          []    -> pure ()
                                          (x:_) -> nonExhaustive x

                   let collect :: Case -> Q (Maybe Name, Maybe Exp, Exp)
                       collect _ = fail "sCase: collect guards: TODO"

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
