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

import Prelude hiding (fail)
import qualified Prelude as P(fail)

import System.FilePath

-- | TH parse trees don't have location. Let's have a simple mechanism to keep track of them for our use case
data Offset = Unknown | OffBy Int Int Int

fail :: Offset -> String -> Q a
fail Unknown         s = P.fail s
fail (OffBy lo co w) s = do loc@Loc{loc_start = (sl, _)} <- location
                            let start = (sl + lo, co + 1)
                                end   = (sl + lo, co + w)
                                newLoc = loc {loc_start = start, loc_end = end}
                            P.fail (fmtLoc newLoc ++ ": " ++  s)
  where fmtLoc loc = takeFileName (loc_filename loc) ++ ":" ++ sh (loc_start loc) (loc_end loc)
        sh ab@(a, b) cd@(c, d) | a == c = show a ++ ":" ++ show b ++ "-" ++ show d
                               | True   = show ab ++ "-" ++ show cd

-- | What kind of case-match are we given. In each case, the last maybe exp is the possible guard.
data Case = CMatch Offset Name (Maybe [Pat]) Exp (Maybe Exp) -- Cstr a b _ c d if maybe, Cstr{} if nothing on pats
          | CWild  Offset                    Exp (Maybe Exp) -- wild-card: _

-- | What's the offset?
caseOffset :: Case -> Offset
caseOffset (CMatch o _ _ _ _) = o
caseOffset (CWild  o     _ _) = o

-- | Show a case nicely
showCase :: Case -> String
showCase sc = case sc of
                CMatch _ c (Just ps) _ mbG -> unwords $ nameBase c : map pprint ps ++ shGuard mbG
                CMatch _ c Nothing   _ mbG -> unwords $ nameBase c : "{}"           : shGuard mbG
                CWild  _             _ mbG -> unwords $ "_"                         : shGuard mbG
 where shGuard Nothing  = []
       shGuard (Just e) = ["|", pprint e]


-- | Get the name of the constructor, if any
getCaseConstructor :: Case -> Maybe Name
getCaseConstructor (CMatch _ nm _ _ _) = Just nm
getCaseConstructor (CWild  _      _ _) = Nothing

-- | Get the guard, if any
getCaseGuard :: Case -> Maybe Exp
getCaseGuard (CMatch _ _ _ _ mbg) = mbg
getCaseGuard (CWild  _     _ mbg) = mbg

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
    bad ctx _ = fail Unknown $ "sCase: not usable in " <> ctx <> " context"

    extract :: String -> ExpQ
    extract src =
      case parts src of
        Nothing -> fail Unknown $ unlines [ "sCase: Failed to parse a symbolic case-expression."
                                          , ""
                                          , "           Instead of:   case      expr of alts"
                                          , "           Write     : [sCase|Type expr of alts|]"
                                          , ""
                                          , "        where Type is the underlying concrete type of the expression."
                                          ]
        Just ((typ, scrutStr), altsStr) -> do
          let fnTok    = "sCase" <> typ
              fullCase = "case " <> scrutStr <> " of " <> altsStr
          case Meta.parseExp fullCase of
            Right (CaseE scrut matches) -> do
              fnName <- lookupValueName fnTok >>= \case
                Just n  -> pure (VarE n)
                Nothing -> fail Unknown $ "sCase: unknown function " <> fnTok
              cases <- mapM (matchToPair src) matches >>= checkCase typ . concat
              buildCase fnName scrut cases
            Right _  -> fail Unknown "sCase: internal parse error, not a case-expression"
            Left err -> case lines err of
                           [l, _, e] -> fail Unknown $ "sCase parse error [Line " <> l <> "]: " <> e
                           _         -> fail Unknown $ "sCase parse error: " <> err

    buildCase caseFunc scrut (Left   cases) = pure $ foldl AppE (caseFunc `AppE` scrut) cases
    buildCase _caseFunc _scrut (Right _chain) = fail Unknown $ "Guarded case TBD"

    getGuards :: Body -> [Dec] -> Q [(Exp, Maybe Exp)]
    getGuards (NormalB  rhs)  locals = pure [(addLocals locals rhs, Nothing)]
    getGuards (GuardedB exps) locals = mapM get exps
      where get (NormalG e,  rhs) = pure (addLocals locals rhs, Just e)
            get (PatG stmts, _)   = fail Unknown $ unlines $  "sCase: Pattern guards are not supported: "
                                                           : ["        " ++ pprint s | s <- stmts]

    -- Turn where clause into simple let
    addLocals :: [Dec] -> Exp -> Exp
    addLocals [] e = e
    addLocals ds e = LetE ds e

    -- Given an occurrence of a name, find what it refers to
    getReference :: Offset -> Name -> Q Name
    getReference off refName = do mbN <- lookupValueName (nameBase refName)
                                  case mbN of
                                    Nothing -> fail off $ "sCase: Not in scope: data constructor: " <> pprint refName
                                    Just n  -> pure n

    matchToPair :: String -> Match -> Q [Case]
    matchToPair entireExp (Match pat grhs locals) = do
      let linesOfExp  = zip [0..] (lines entireExp)
          getOffset w = walk (maybe ("_", "_") (\n -> (pprint n, nameBase n)) w) linesOfExp
            where walk _ []           = Unknown
                  walk m ((lo, l):ls) = case find 0 l of
                                          Just (co, wdth) -> OffBy lo co wdth
                                          Nothing         -> walk m ls
                    where find _ "" = Nothing
                          find co s
                             | cur == [fst m] = Just (co + length (takeWhile isSpace s), length (fst m))
                             | cur == [snd m] = Just (co + length (takeWhile isSpace s), length (snd m))
                             | True           = find (co + length pre + 1) (drop 1 post)
                            where cur         = take 1 (map (takeWhile (`notElem` "{")) (words s))
                                  (pre, post) = break (== ';') s

      rhss <- getGuards grhs locals
      case pat of
        ConP conName _ subpats -> do let off = getOffset (Just conName)
                                     ps  <- traverse (patToVar off) subpats
                                     con <- getReference off conName
                                     pure [CMatch off con (Just ps) rhs t | (rhs, t) <- rhss]
        RecP conName []        -> do let off = getOffset (Just conName)
                                     con <- getReference off conName
                                     pure [CMatch off                 con Nothing   rhs t | (rhs, t) <- rhss]
        WildP                  ->    pure [CWild  (getOffset Nothing)               rhs t | (rhs, t) <- rhss]
        _ -> fail Unknown $ unlines [ "sCase: Unsupported pattern:"
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
        let hasCatchAll = or [True | CWild _ _ Nothing <- cases]

        -- Step 0: If there's an unguarded wild-card, make sure nothing else follows it.
        -- Note that this also handles wild-card being present twice.
        let checkWild []                         = pure ()
            checkWild (CMatch{}          : rest) = checkWild rest
            checkWild (CWild _ _ Just{}  : rest) = checkWild rest
            checkWild (CWild o _ Nothing : rest) = case rest of
                                                  []  -> pure ()
                                                  red  -> let w | length red > 1 = "matches are"
                                                                | True           = "match is"
                                                          in fail o $ unlines $ ("sCase: Pattern " ++ w ++ " redundant")
                                                                              : ["        " ++ showCase r | r <- red]
        checkWild cases

        -- Step 2: Make sure every constructor listed actually exists and matches in arity.
        let chk1 :: Case -> Q ()
            chk1 c = case c of
                       CMatch o nm ps _ _ -> isSafe o nm (length <$> ps)
                       CWild  _       _ _ -> pure ()
              where isSafe :: Offset -> Name -> Maybe Int -> Q ()
                    isSafe o nm mbLen
                      | Just ts <- nm `lookup` cstrs
                      = case mbLen of
                           Nothing  -> pure ()
                           Just cnt -> unless (length ts == cnt)
                                            $ fail o $ unlines [ "sCase: Arity mismatch."
                                                               , "        Type       : " ++ typ
                                                               , "        Constructor: " ++ pprint nm
                                                               , "        Expected   : " ++ show (length ts)
                                                               , "        Given      : " ++ show cnt
                                                               ]
                      | True
                      = fail o $ unlines [ "sCase: Unknown constructor:"
                                         , "        Type          : " ++ typ
                                         , "        Saw           : " ++ pprint nm
                                         , "        Must be one of: " ++ intercalate ", " (map (pprint . fst) cstrs)
                                         ]

        mapM_ chk1 cases

        -- Step 2: Make sure constructors matches are not overlapping
        let problem w x = fail (caseOffset x) $ unlines [ "sCase: " ++ w ++ ":"
                                                        , "        Type       : " ++ typ
                                                        , "        Constructor: " ++ showCase x
                                                        ]

            overlap   = problem "Overlapping case constructors"
            unmatched = problem "Non-exhaustive match"

            nonExhaustive o cstr = fail o $ unlines [ "sCase: Pattern match(es) are non-exhaustive."
                                                    , "        Not matched     : " ++ pprint cstr
                                                    , "        Patterns of type: " ++ typ
                                                    , "        Must match each : " ++ intercalate ", " (map (pprint . fst) cstrs)
                                                    , ""
                                                    , "      You can use a '_' to match multiple cases."
                                                    ]
            -- We're done
            chk2 [] = pure ()

            -- If we have a guarded match, then this guard can fail. So either there must be a match
            -- for it later on, or there must be a catch-all. Note that if it exists later, we don't
            -- care if that occurrence is guarded or not; because if it is guarded, we'll fail on the last one.
            chk2 (c@(CMatch _ nm _ _ (Just {})) : rest)
              | hasCatchAll || Just nm `elem` map getCaseConstructor rest
              = chk2 rest
              | True
              = unmatched c

            -- If we have a non-guarded match, then there must be no matches for this constructor later on
            chk2 (c@(CMatch _ nm _ _ Nothing) : rest)
              | Just nm `elem` map getCaseConstructor rest
              = overlap c
              | True
              = chk2 rest

            -- If there's a guarded wildcard, must make sure there's a catch all afterwards
            chk2 (c@(CWild _ _ Just{}) : rest)
              | hasCatchAll
              = chk2 rest
              | True
              = unmatched c

            -- No need to worry about anything following catch-all, since we already covered that before
            chk2 (CWild _ _ Nothing : rest) = chk2 rest

        chk2 cases

        -- At this point, we either have a simple case with no guards, in which case
        -- we translate this to an sCase for that type. So find all alternatives.
        -- Otherwise, this will become an ite-chain
        let hasGuards = any isGuarded cases

        if not hasGuards
           then do defaultCase <- case [((e, mbg), c) | c@(CWild _ e mbg) <- cases] of
                                    []                  -> pure $ Nothing
                                    [((e, Nothing), c)] -> pure $ Just (caseOffset c, e)
                                    cs@((_, c):_)       -> fail (caseOffset c)
                                                         $ unlines $   "sCase: Impossible happened; found unexpected cases:"
                                                                   :  [ "        " ++ showCase curc | curc <- map snd cs]
                                                                   ++ [ ""
                                                                      , "      Please report this as a bug."
                                                                      ]
                   let find _ []     = Nothing
                       find w (c:cs)
                         | matches = Just c
                         | True    = find w cs
                         where matches = case c of
                                           CMatch _ nm _ _ _ -> nm == w
                                           CWild  _      _ _ -> False

                       case2rhs :: Case -> [Type] -> (Maybe Exp, Exp)
                       case2rhs cs ts = (LamE pats <$> mbGuard, LamE pats e)
                         where (mbGuard, e, pats) = case cs of
                                                      CMatch _ _ (Just ps) rhs mbt -> (mbt, rhs, ps)
                                                      CMatch _ _ Nothing   rhs mbt -> (mbt, rhs, map (const WildP) ts)
                                                      CWild  _             rhs mbt -> (mbt, rhs, map (const WildP) ts)

                       collect (cstr, ts)
                         | Just e <- find cstr cases
                         = pure $ case2rhs e ts
                         | True
                         = case defaultCase of
                             Nothing -> nonExhaustive Unknown cstr
                             Just (_, de) -> do let ps = map (const WildP) ts
                                                pure (Nothing, LamE ps de)

                   res <- mapM collect cstrs

                   -- If we reached here, all is well; except we might have an extra wildcard that we did not use
                   when (length cases > length cstrs) $
                     case defaultCase of
                       Nothing     -> pure ()
                       Just (o, _) -> fail o "sCase: Wildcard match is redundant"

                   -- Double check that we had no guards and return the cases
                   case [r | (Just{}, r) <- res] of
                     [] -> pure $ Left $ map snd res
                     rs -> fail Unknown $ unlines $    "sCase: Impossible happened; found a guard in no-guard case."
                                                  :  [ "        " ++ pprint r | r <- rs]
                                                  ++ [ ""
                                                    , "      Please report this as a bug."
                                                    ]

           else do -- We have guards.

                   -- Collect, for each constructor, the corresponding cases:
                   let cstrMatches :: [(Name, ([Type], [Case]))]
                       cstrMatches = map (\(cstr, ts) -> (cstr, (ts, concatMap (matches cstr) cases))) cstrs
                         where matches cstr c | Just n <- getCaseConstructor c, n == cstr = [c]
                                              | True                                      = []

                   -- Make sure we have a match for every constructor or a catch-all
                   unless hasCatchAll $ case [nm | (nm, (_, [])) <- cstrMatches] of
                                          []    -> pure ()
                                          (x:_) -> nonExhaustive Unknown x

                   let collect :: Case -> Q (Maybe Name, Maybe Exp, Exp)
                       collect c = fail (caseOffset c) "sCase: collect guards: TODO"

                   res <- mapM collect cases
                   pure $ Right res

    patToVar :: Offset -> Pat -> Q Pat
    patToVar _ p@VarP{} = pure p
    patToVar _ p@WildP  = pure p
    patToVar o p        = fail o $ "sCase: constructor arguments must be variables, not: " <> pprint p

    parts = go ""
      where go _     ""             = Nothing
            go sofar ('o':'f':rest) = Just (break isSpace (dropWhile isSpace (reverse sofar)), rest)
            go sofar (c:cs)         = go (c:sofar) cs
