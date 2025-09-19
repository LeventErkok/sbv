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
-- where @Expr@ is the underlying type.
-----------------------------------------------------------------------------

{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.SCase (sCase) where

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import qualified Language.Haskell.Meta.Parse as Meta

import qualified Language.Haskell.Exts as E

import Control.Monad (unless, when, zipWithM)

import Data.SBV.Client (getConstructors)
import Data.SBV.Core.Model (ite, sym)
import Data.SBV.Core.Data  (sTrue, (.&&))

import Data.Char  (isSpace, isDigit)
import Data.List  (intercalate)
import Data.Maybe (isJust, fromMaybe)

import Prelude hiding (fail)
import qualified Prelude as P(fail)

import Data.Generics
import qualified Data.Set as Set
import Data.Set (Set)

import System.FilePath

-- | TH parse trees don't have location. Let's have a simple mechanism to keep track of them for our use case
data Offset = Unknown | OffBy Int Int Int
 deriving Show

-- | Better fail method, keeping track of offsets
fail :: Offset -> String -> Q a
fail Unknown     s = P.fail s
fail off@OffBy{} s = do loc <- location
                        P.fail (fmtLoc loc off ++ ": " ++  s)

-- | Format a given location by the offset
fmtLoc :: Loc -> Offset -> String
fmtLoc loc@Loc{loc_start = (sl, _)} off = takeFileName (loc_filename newLoc) ++ ":" ++ sh (loc_start newLoc) (loc_end newLoc)
  where sh ab@(a, b) cd@(c, d) | a == c = show a ++ ":" ++ show b ++ if b == d then "" else '-' : show d
                               | True   = show ab ++ "-" ++ show cd

        newLoc = case off of
                   Unknown       -> loc
                   OffBy lo co w -> loc {loc_start = (sl + lo, co + 1), loc_end = (sl + lo, co + w)}

-- | What kind of case-match are we given. In each case, the last maybe exp is the possible guard.
data Case = CMatch Offset          -- regular match
                   Name            -- name of the constructor
                   (Maybe [Pat])   -- [a, b, c] in C a b c. Or Nothing if C{}
                   (Maybe Exp)     -- guard
                   Exp             -- rhs
                   (Set Name)      -- All variables used all RHSs and All guards
          | CWild  Offset          -- wild card
                   (Maybe Exp)     -- guard
                   Exp             -- rhs

-- | What's the offset?
caseOffset :: Case -> Offset
caseOffset (CMatch o _ _ _ _ _) = o
caseOffset (CWild  o       _ _) = o

-- | Show a case nicely
showCase :: Case -> String
showCase = showCaseGen Nothing

-- | Show a case nicely, with location
showCaseGen :: Maybe Loc -> Case -> String
showCaseGen mbLoc sc = case sc of
                         CMatch _ c (Just ps) mbG _ _ -> loc ++ unwords (nameBase c : map pprint ps ++ shGuard mbG)
                         CMatch _ c Nothing   mbG _ _ -> loc ++ unwords (nameBase c : "{}"           : shGuard mbG)
                         CWild  _             mbG _   -> loc ++ unwords ("_"                         : shGuard mbG)
 where shGuard Nothing  = []
       shGuard (Just e) = ["|", pprint e]

       loc = case mbLoc of
               Nothing -> ""
               Just l  -> fmtLoc l (caseOffset sc) ++ ": "

-- | Get the name of the constructor, if any
getCaseConstructor :: Case -> Maybe Name
getCaseConstructor (CMatch _ nm _ _ _ _) = Just nm
getCaseConstructor CWild{}               = Nothing

-- | Get the guard, if any
getCaseGuard :: Case -> Maybe Exp
getCaseGuard (CMatch _ _ _ mbg _ _) = mbg
getCaseGuard (CWild  _     mbg _  ) = mbg

-- | Is there a guard?
isGuarded :: Case -> Bool
isGuarded = isJust . getCaseGuard

-- | Find offset of each successive match. This isn't perfect, but it does the job
findOffsets :: String -> [Offset]
findOffsets s = analyze $ E.parseExpWithMode E.defaultParseMode $ "case ()" ++ tab ++ rest
  where rest = relevant s
        -- there's a chance the replication below might yield a negative value, which can make our
        -- offset calculation slightly off. But this should be exceedingly rare because it'd have to be that
        -- matches are on the same line and the "Type expr" part of the original must be shorter than 7 chars.
        -- Let's ignore that possibility.
        tab  = replicate (length s - length rest - 7) ' '
        relevant r@(' ':'o':'f':_) = r
        relevant ""                = ""
        relevant (_:cs)            = relevant cs

        analyze E.ParseFailed{} = [] -- Just ignore
        analyze (E.ParseOk e)   = case e of
                                   E.Case _ _ alts -> map getOff alts
                                   _               -> []
          where getOff (E.Alt l p _ _) = OffBy (E.srcSpanStartLine as - 1) (E.srcSpanStartColumn as - 1) w
                   where as = E.srcInfoSpan l
                         cs = E.srcInfoSpan (E.ann p)
                         w  = E.srcSpanEndColumn cs - E.srcSpanStartColumn cs

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
              offsets  = findOffsets src
          case Meta.parseExp fullCase of
            Right (CaseE scrut matches) -> do
              fnName <- lookupValueName fnTok >>= \case
                Just n  -> pure (VarE n)
                Nothing -> fail Unknown $ unlines [ "sCase: Unknown symbolic ADT: " <> typ
                                                  , ""
                                                  , "        To use a symbolic case expression, declare your ADT, and then:"
                                                  , "             mkSymbolic ''" <> typ
                                                  , "        In a template-haskell context."
                                                  ]
              cases <- zipWithM matchToPair (offsets ++ repeat Unknown) matches >>= checkCase scrut typ . concat
              buildCase typ fnName scrut cases
            Right _  -> fail Unknown "sCase: Parse error, cannot extract a case-expression."
            Left err -> case lines err of
                          (_:loc:res) | ["SrcLoc", _, l, c] <- words loc, all isDigit l, all isDigit c
                             -> fail (OffBy (read l - 1) (read c - 1) 1) (unlines res)
                          _  -> fail Unknown $ "sCase parse error: " <> err

    buildCase _    caseFunc  scrut (Left  cases) = pure $ foldl AppE (caseFunc `AppE` scrut) cases
    buildCase typ _caseFunc _scrut (Right cases) = iteChain cases
      where iteChain []              = pure $ AppE (VarE 'sym) (LitE (StringL ("unmatched_sCase|" ++ typ)))
            iteChain ((t, e) : rest) = do r <- iteChain rest
                                          pure $ foldl AppE (VarE 'ite) [t, e, r]

    getGuards :: Body -> [Dec] -> Q [(Maybe Exp, Exp)]
    getGuards (NormalB  rhs)  locals = pure [(Nothing, addLocals locals rhs)]
    getGuards (GuardedB exps) locals = mapM get exps
      where get (NormalG e,  rhs)
              | isSTrue e
              = pure (Nothing, addLocals locals rhs)
              | True
              = pure (Just e, addLocals locals rhs)
            get (PatG stmts, _)   = fail Unknown $ unlines $  "sCase: Pattern guards are not supported: "
                                                           : ["        " ++ pprint s | s <- stmts]

            -- Is this literally sTrue? This is a bit dangerous since
            -- we just look at the base-name, but good enough
            isSTrue (VarE nm) = nameBase nm == nameBase 'sTrue
            isSTrue _         = False

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

    matchToPair :: Offset -> Match -> Q [Case]
    matchToPair off (Match pat grhs locals) = do
      rhss <- getGuards grhs locals
      let allUsed = Set.unions (map (\(mbG, e) -> maybe Set.empty freeVars mbG `Set.union` freeVars e) rhss)

      case pat of
        ConP conName _ subpats -> do ps  <- traverse (patToVar off) subpats
                                     con <- getReference off conName
                                     pure [CMatch off con (Just ps) mbG rhs allUsed | (mbG, rhs) <- rhss]

        RecP conName []        -> do con <- getReference off conName
                                     pure [CMatch off con Nothing   mbG rhs allUsed | (mbG, rhs) <- rhss]

        WildP                  ->    pure [CWild  off               mbG rhs         | (mbG, rhs) <- rhss]

        _ -> fail Unknown $ unlines [ "sCase: Unsupported pattern:"
                                    , "            Saw: " <> pprint pat
                                    , ""
                                    , "        Only constructors with variables (i.e., Cstr a b _ d)"
                                    , "        Empty record matches (i.e., Cstr{})"
                                    , "        And wildcards (i.e., _) for default"
                                    , "        are supported."
                                    ]

    -- Make sure things are in good-shape and decide if we have guards
    checkCase :: Exp -> String -> [Case] -> Q (Either [Exp] [(Exp, Exp)])
    checkCase scrut typ cases = do
        loc   <- location

        cstrs <- -- We don't need the field names if user supplied them; so drop them here
                 let dropFieldNames (c, nts) = (c, map snd nts)
                 in map dropFieldNames <$> snd <$> getConstructors (mkName typ)

        -- Is there a catch all clause?
        let hasCatchAll = or [True | CWild _ Nothing _ <- cases]

        -- Step 0: If there's an unguarded wild-card, make sure nothing else follows it.
        -- Note that this also handles wild-card being present twice.
        let checkWild []                         = pure ()
            checkWild (CMatch{}          : rest) = checkWild rest
            checkWild (CWild _ Just{}  _ : rest) = checkWild rest
            checkWild (CWild o Nothing _ : rest) =
                  case rest of
                    []  -> pure ()
                    red  -> fail o $ unlines $ "sCase: Wildcard makes the remaining matches redundant:"
                                             : ["        " ++ showCaseGen (Just loc) r | r <- red]
        checkWild cases

        -- Step 2: Make sure every constructor listed actually exists and matches in arity.
        let chk1 :: Case -> Q ()
            chk1 c = case c of
                       CMatch o nm ps _ _ _ -> isSafe o nm (length <$> ps)
                       CWild  {}            -> pure ()
              where isSafe :: Offset -> Name -> Maybe Int -> Q ()
                    isSafe o nm mbLen
                      | Just ts <- nm `lookup` cstrs
                      = case mbLen of
                           Nothing  -> pure ()
                           Just cnt -> unless (length ts == cnt)
                                            $ fail o $ unlines [ "sCase: Arity mismatch."
                                                               , "        Type       : " ++ typ
                                                               , "        Constructor: " ++ nameBase nm
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

        -- Step 2: Make sure constructor matches are not overlapping
        let problem w extras x = fail (caseOffset x) $ unlines $ [ "sCase: " ++ w ++ ":"
                                                                 , "        Type       : " ++ typ
                                                                 , "        Constructor: " ++ showCase x
                                                                 ]
                                                              ++ [ "      " ++ e | e <- extras]

            overlap x xs = problem "Overlapping case constructors" extras x
              where extras = "Overlaps with:" : ["  " ++ p | p <- map (showCaseGen (Just loc)) xs]

            unmatched x
             | isGuarded x = problem "Non-exhaustive match" ["NB. Guarded match might fail."] x
             | True        = problem "Non-exhaustive match" []                                x

            nonExhaustive o cstr = fail o $ unlines [ "sCase: Pattern match(es) are non-exhaustive."
                                                    , "        Not matched     : " ++ nameBase cstr
                                                    , "        Patterns of type: " ++ typ
                                                    , "        Must match each : " ++ intercalate ", " (map (nameBase . fst) cstrs)
                                                    , ""
                                                    , "      You can use a '_' to match multiple cases."
                                                    ]
            -- We're done
            chk2 [] = pure ()

            -- If we have a non-guarded match, then there must be no matches for this constructor later on. If so, they're redundant.
            chk2 (c@(CMatch _ nm _ Nothing _ _) : rest)
              = case filter (\oc -> getCaseConstructor oc == Just nm) rest of
                  [] -> chk2 rest
                  os -> overlap (last os) (c : init os)

            -- If we have a guarded match, then this guard can fail. So either there must be a match
            -- for it later on, or there must be a catch-all. Note that if it exists later, we don't
            -- care if that occurrence is guarded or not; because if it is guarded, we'll fail on the last one.
            chk2 (c@(CMatch _ nm _ Just{} _ _) : rest)
              | hasCatchAll || Just nm `elem` map getCaseConstructor rest
              = chk2 rest
              | True
              = unmatched c

            -- If there's a guarded wildcard, must make sure there's a catch all afterwards
            chk2 (c@(CWild _ Just{} _) : rest)
              | hasCatchAll
              = chk2 rest
              | True
              = unmatched c

            -- No need to worry about anything following catch-all, since we already covered that before
            chk2 (CWild _ Nothing _ : rest) = chk2 rest

        chk2 cases

        -- At this point, we either have a simple case with no guards, in which case
        -- we translate this to an sCase for that type. So find all alternatives.
        -- Otherwise, this will become an ite-chain
        let hasGuards = any isGuarded cases

        if not hasGuards
           then do defaultCase <- case [((e, mbg), c) | c@(CWild _ mbg e) <- cases] of
                                    []                  -> pure Nothing
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
                                           CMatch _ nm _ _ _ _ -> nm == w
                                           CWild  {}           -> False

                       case2rhs :: Case -> [Type] -> (Maybe Exp, Exp)
                       case2rhs cs ts = (LamE pats <$> mbGuard, LamE pats e)
                         where (mbGuard, e, pats) = case cs of
                                                      CMatch _ _ (Just ps) mbG rhs _ -> (mbG, rhs, ps)
                                                      CMatch _ _ Nothing   mbG rhs _ -> (mbG, rhs, map (const WildP) ts)
                                                      CWild  _             mbG rhs   -> (mbG, rhs, map (const WildP) ts)

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
                   defaultCase <- case [(c, e) | c@(CWild _ Nothing e) <- cases] of
                                    []         -> pure Nothing
                                    ((c, e):_) -> pure $ Just (caseOffset c, e)

                   -- Collect, for each constructor, the corresponding cases:
                   let cstrMatches :: [(Name, ([Type], [Case]))]
                       cstrMatches = map (\(cstr, ts) -> (cstr, (ts, concatMap (matches cstr) cases))) cstrs
                         where matches cstr c | Just n <- getCaseConstructor c, n == cstr = [c]
                                              | True                                      = []

                   -- Make sure we have a match for every constructor or a catch-all
                   unless hasCatchAll $ case [nm | (nm, (_, [])) <- cstrMatches] of
                                          []    -> pure ()
                                          (x:_) -> nonExhaustive Unknown x

                   -- If every constructor have a full match, then catch-all, if exists, is redundant:
                   case defaultCase of
                     Nothing     -> pure ()
                     Just (o, _)
                       | map fst cstrs == [nm | (nm, (_, cs)) <- cstrMatches, not (all isGuarded cs)]
                       -> fail o "sCase: Wildcard match is redundant"
                       | True
                       -> pure ()

                   let collect :: Case -> Q (Exp, Exp)
                       collect (CWild  _        mbG rhs        ) = pure (fromMaybe (VarE 'sTrue) mbG, rhs)
                       collect (CMatch o nm mbp mbG rhs allUsed) = do
                           case nm `lookup` cstrs of
                             Nothing -> fail o $ unlines [ "sCase: Impossible happened."
                                                         , "        Unable to determine params for: " <> pprint nm
                                                         ]
                             Just ts -> do let pats = fromMaybe (map (const WildP) ts) mbp
                                               args = [ AppE (VarE (mkName ("get" ++ nameBase nm ++ "_" ++ show i))) scrut
                                                      | (i, _) <- zip [(1 :: Int) ..] ts]
                                               rec  = VarE $ mkName $ "is" ++ nameBase nm

                                               -- What are the free variables in the guard and the rhs that we bind?
                                               used    = Set.fromList [n | VarP n <- pats] `Set.intersection` allUsed
                                               close e = foldr1 (AppE . AppE (VarE 'const)) (e:extras)
                                                 where extras = map VarE $ Set.toList (used Set.\\ freeVars e)

                                               mkApp f | null pats = f
                                                       | True      = foldl AppE (LamE pats f) args

                                               grd :: Exp
                                               grd = case mbG of
                                                       Nothing -> AppE rec scrut
                                                       Just g  -> foldl1 AppE [VarE '(.&&), AppE rec scrut, mkApp (close g)]

                                           pure (grd, mkApp (close rhs))

                   Right <$> mapM collect cases

    patToVar :: Offset -> Pat -> Q Pat
    patToVar _ p@VarP{} = pure p
    patToVar _ p@WildP  = pure p
    patToVar o p        = fail o $ unlines [ "sCase: Unsupported complex pattern match."
                                           , "        Saw: " <> pprint p
                                           , ""
                                           , "      Only variables and wild-card are supported."
                                           ]
    parts = go ""
      where go _     ""             = Nothing
            go sofar ('o':'f':rest) = Just (break isSpace (dropWhile isSpace (reverse sofar)), rest)
            go sofar (c:cs)         = go (c:sofar) cs

-- | Free variables = used – bound
freeVars :: Exp -> Set Name
freeVars e = usedVars e Set.\\ boundVars e
 where boundVars :: Exp -> Set Name
       boundVars = everything Set.union (mkQ Set.empty f)
         where f :: Pat -> Set Name
               f (VarP n)  = Set.singleton n
               f (AsP n _) = Set.singleton n
               f _         = Set.empty

       usedVars :: Exp -> Set Name
       usedVars = everything Set.union (mkQ Set.empty f)
         where f :: Exp -> Set Name
               f (VarE n) = Set.singleton n
               f _        = Set.empty
