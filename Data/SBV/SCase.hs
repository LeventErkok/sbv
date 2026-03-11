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
--
-- Also provides `[pCase|Expr expr of ... |]` for proof case-splits.
-----------------------------------------------------------------------------

{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.SCase (sCase, pCase) where

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import qualified Language.Haskell.Meta.Parse            as Meta
import qualified Language.Haskell.Meta.Syntax.Translate as Meta

import qualified Language.Haskell.Exts as E

import Control.Monad (unless, when, zipWithM)

import Data.SBV.Client (getConstructors)
import Data.SBV.Core.Model (ite, sym)
import Data.SBV.Core.Data  (sTrue, sNot, (.&&), (.||), (.==), (.===), literal)

import qualified Data.SBV.List  as SL
import qualified Data.SBV.Tuple as ST
import qualified Data.SBV.Maybe as SM
import qualified Data.SBV.Either as SE

import Data.Char  (isSpace, isDigit)
import Data.List  (intercalate, stripPrefix)
import Data.Maybe (isJust, fromMaybe)

import Prelude hiding (fail)
import qualified Prelude as P(fail)

import Data.Generics
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import System.FilePath

-- | Conjoin a list of TH boolean expressions with (.&&), filtering out trivially true guards.
sAndAll :: [Exp] -> Exp
sAndAll = go . filter (not . isTriviallyTrue)
  where go []  = VarE 'sTrue
        go [g] = g
        go gs  = foldr1 (\a b -> foldl1 AppE [VarE '(.&&), a, b]) gs

        isTriviallyTrue (VarE nm) = nameBase nm == nameBase 'sTrue
        isTriviallyTrue (ConE nm) = nameBase nm == "True"
        isTriviallyTrue _         = False

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

-- | Built-in types recognized by sCase/pCase. Maybe and Either do have mkSymbolic-generated
-- infrastructure, but we treat them as built-in so that the generated code uses TH-quoted names
-- (which resolve at SCase.hs compile time) instead of mkName-based references (which would
-- require the user to have the testers/accessors in scope at the splice site).
data BuiltinType = BTMaybe | BTEither | BTList | BTTuple Int
  deriving Show

-- | Compare two Names by their base (unqualified) name. This is needed because
-- built-in constructor names (created with mkName) won't match the fully-qualified
-- names that GHC resolves patterns to (e.g., mkName "Nothing" vs GHC.Internal.Maybe.Nothing).
-- Since constructor names are unique within a type, comparing by nameBase is safe.
sameBase :: Name -> Name -> Bool
sameBase a b = nameBase a == nameBase b

-- | Lookup by nameBase instead of Name equality.
lookupBase :: Name -> [(Name, a)] -> Maybe a
lookupBase _  []          = Nothing
lookupBase nm ((k,v):kvs)
  | sameBase nm k = Just v
  | otherwise     = lookupBase nm kvs

-- | Recognize built-in type names.
recognizeBuiltin :: String -> Maybe BuiltinType
recognizeBuiltin "Maybe"  = Just BTMaybe
recognizeBuiltin "Either" = Just BTEither
recognizeBuiltin "List"   = Just BTList
recognizeBuiltin s
  | Just n <- stripPrefix "Tuple" s, not (null n), all isDigit n, let k = read n, k >= 2, k <= 8
  = Just (BTTuple k)
recognizeBuiltin _ = Nothing

-- | Recognize a constructor name as belonging to a built-in type. Used in flattenPat
-- to generate TH-quoted tester/accessor references for nested built-in constructors.
recognizeBuiltinCon :: String -> Maybe BuiltinType
recognizeBuiltinCon "Nothing" = Just BTMaybe
recognizeBuiltinCon "Just"    = Just BTMaybe
recognizeBuiltinCon "Left"    = Just BTEither
recognizeBuiltinCon "Right"   = Just BTEither
recognizeBuiltinCon _         = Nothing

-- | Constructor info for a built-in type: (name, arity).
builtinConstructors :: BuiltinType -> [(Name, Int)]
builtinConstructors BTMaybe       = [(mkName "Nothing", 0), (mkName "Just", 1)]
builtinConstructors BTEither      = [(mkName "Left", 1), (mkName "Right", 1)]
builtinConstructors BTList        = [(mkName "[]", 0), (mkName ":", 2)]
builtinConstructors (BTTuple n)   = [(tupleDataName n, n)]

-- | Generate a tester expression for a built-in type constructor.
builtinTester :: BuiltinType -> Name -> Exp -> Exp
builtinTester BTMaybe nm scrut
  | nameBase nm == "Nothing" = AppE (VarE 'SM.isNothing) scrut
  | nameBase nm == "Just"    = AppE (VarE 'SM.isJust)    scrut
builtinTester BTEither nm scrut
  | nameBase nm == "Left"  = AppE (VarE 'SE.isLeft)  scrut
  | nameBase nm == "Right" = AppE (VarE 'SE.isRight) scrut
builtinTester BTList nm scrut
  | nameBase nm == "[]" = AppE (VarE 'SL.null) scrut
  | nameBase nm == ":"  = AppE (VarE 'sNot) (AppE (VarE 'SL.null) scrut)
builtinTester (BTTuple _) _ _ = VarE 'sTrue
builtinTester bt nm _ = error $ "sCase: builtinTester: unexpected constructor " ++ nameBase nm ++ " for " ++ show bt

-- | Generate an accessor expression for a built-in type constructor field.
builtinAccessor :: BuiltinType -> Name -> Int -> Exp -> Exp
builtinAccessor BTMaybe nm i scrut
  | nameBase nm == "Just", i == 1 = AppE (VarE 'SM.getJust_1) scrut
builtinAccessor BTEither nm i scrut
  | nameBase nm == "Left",  i == 1 = AppE (VarE 'SE.getLeft_1)  scrut
  | nameBase nm == "Right", i == 1 = AppE (VarE 'SE.getRight_1) scrut
builtinAccessor BTList nm i scrut
  | nameBase nm == ":", i == 1 = AppE (VarE 'SL.head) scrut
  | nameBase nm == ":", i == 2 = AppE (VarE 'SL.tail) scrut
builtinAccessor (BTTuple _) _ i scrut
  -- Simplify _i (tuple (a, b, ...)) to just the i-th component
  | AppE (VarE f) (TupE components) <- scrut
  , nameBase f == "tuple"
  , let cs = [e | Just e <- components]
  , i >= 1, i <= length cs
  = cs !! (i - 1)
  | otherwise
  = AppE (VarE (tupleAccessorName i)) scrut
  where tupleAccessorName 1 = 'ST._1
        tupleAccessorName 2 = 'ST._2
        tupleAccessorName 3 = 'ST._3
        tupleAccessorName 4 = 'ST._4
        tupleAccessorName 5 = 'ST._5
        tupleAccessorName 6 = 'ST._6
        tupleAccessorName 7 = 'ST._7
        tupleAccessorName 8 = 'ST._8
        tupleAccessorName n = error $ "sCase: tupleAccessorName: unsupported index " ++ show n
builtinAccessor bt nm i _ = error $ "sCase: builtinAccessor: unexpected constructor " ++ nameBase nm ++ " field " ++ show i ++ " for " ++ show bt

-- | Generate a tester expression for a constructor, dispatching to builtinTester for
-- recognized built-in constructors or falling back to @is\<Con\>@ for user ADTs.
mkTester :: Name -> Exp -> Exp
mkTester nm scrut = case recognizeBuiltinCon (nameBase nm) of
    Just bt -> builtinTester bt nm scrut
    Nothing -> AppE (VarE (mkName ("is" ++ nameBase nm))) scrut

-- | Generate an accessor expression for a constructor field, dispatching to builtinAccessor for
-- recognized built-in constructors or falling back to @get\<Con\>_i@ for user ADTs.
mkAccessor :: Name -> Int -> Exp -> Exp
mkAccessor nm i scrut = case recognizeBuiltinCon (nameBase nm) of
    Just bt -> builtinAccessor bt nm i scrut
    Nothing -> AppE (VarE (mkName ("get" ++ nameBase nm ++ "_" ++ show i))) scrut

-- | Like 'mkTester', but when the built-in type is already known from the scrutinee type.
-- Used in top-level sCase/pCase code generation where 'mbt' is available.
mkTesterFor :: Maybe BuiltinType -> Name -> Exp -> Exp
mkTesterFor (Just bt) nm scrut = builtinTester bt nm scrut
mkTesterFor Nothing   nm scrut = AppE (VarE (mkName ("is" ++ nameBase nm))) scrut

-- | Like 'mkAccessor', but when the built-in type is already known from the scrutinee type.
mkAccessorFor :: Maybe BuiltinType -> Name -> Int -> Exp -> Exp
mkAccessorFor (Just bt) nm i scrut = builtinAccessor bt nm i scrut
mkAccessorFor Nothing   nm i scrut = AppE (VarE (mkName ("get" ++ nameBase nm ++ "_" ++ show i))) scrut

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

-- * Shared parsing infrastructure

-- | Parse a Haskell expression using haskell-src-exts
metaParse :: String -> Either String Exp
metaParse = fmap Meta.toExp . Meta.parseResultToEither . E.parseExpWithMode pm
  where pm = E.defaultParseMode { E.parseFilename = []
                                , E.baseLanguage  = E.Haskell2010
                                , E.extensions = map E.EnableExtension (exts ++ extras)
                                }
        exts = [ E.PostfixOperators
               , E.QuasiQuotes
               , E.UnicodeSyntax
               , E.PatternSignatures
               , E.MagicHash
               , E.ForeignFunctionInterface
               , E.TemplateHaskell
               , E.RankNTypes
               , E.MultiParamTypeClasses
               , E.RecursiveDo
               , E.TypeApplications
               ]

        -- The above just mimics the defaults. These our extras.
        extras = [E.DataKinds]

-- | Split the quasiquote input into (type, scrutinee) and alternatives
parts :: String -> Maybe ((String, String), String)
parts = go ""
  where go _     ""             = Nothing
        go sofar ('o':'f':rest) = Just (break isSpace (dropWhile isSpace (reverse sofar)), rest)
        go sofar (c:cs)         = go (c:sofar) cs

-- | Extract guards from a match body
getGuards :: Body -> [Dec] -> Q [(Maybe Exp, Exp)]
getGuards (NormalB  rhs)  locals = pure [(Nothing, addLocals locals rhs)]
getGuards (GuardedB exps) locals = mapM get exps
  where get (NormalG e,  rhs)
          | isSTrue e
          = pure (Nothing, addLocals locals rhs)
          | True
          = pure (Just e, addLocals locals rhs)
        get (PatG stmts, rhs)
          | all isNoBindS stmts
          = let guards = [e | NoBindS e <- stmts]
                conj   = sAndAll guards
            in pure (if isSTrue conj then Nothing else Just conj, addLocals locals rhs)
          | True
          = fail Unknown $ unlines $  "sCase/pCase: Pattern guards are not supported: "
                                   : ["        " ++ pprint s | s <- stmts]
          where isNoBindS (NoBindS _) = True
                isNoBindS _           = False

        -- Is this literally sTrue (or True)? This is a bit dangerous since
        -- we just look at the base-name, but good enough
        isSTrue (VarE  nm) = nameBase nm == nameBase 'sTrue
        isSTrue (ConE  nm) = nameBase nm == "True"
        isSTrue _          = False

-- | Turn where clause into simple let
addLocals :: [Dec] -> Exp -> Exp
addLocals [] e = e
addLocals ds e = LetE ds e

-- | Given an occurrence of a name, find what it refers to
getReference :: Offset -> Name -> Q Name
getReference off refName = do mbN <- lookupValueName (nameBase refName)
                              case mbN of
                                Nothing -> fail off $ "sCase/pCase: Not in scope: data constructor: " <> pprint refName
                                Just n  -> pure n

-- | Convert a match into a list of cases
matchToPair :: Exp -> Offset -> Match -> Q [Case]
matchToPair scrut off (Match pat grhs locals) = do
  rhss <- getGuards grhs locals
  let allUsed = Set.unions (map (\(mbG, e) -> maybe Set.empty freeVars mbG `Set.union` freeVars e) rhss)

      -- Common logic for constructor-like patterns: flatten sub-patterns, merge synthetic guards
      flattenAndMerge :: Name -> (Int -> Exp) -> [Pat] -> Q [Case]
      flattenAndMerge con accessor subpats = do
          flatResults <- zipWithM (flattenPat off . accessor) [(1::Int)..] subpats
          let ps      = map fstOf3 flatResults
              subGrds = concatMap sndOf3 flatResults
              subDecs = concatMap thdOf3 flatResults

              merge (mbG, rhs) =
                let usedInRhs  = freeVars rhs
                    usedInGrd  = maybe Set.empty freeVars mbG
                    decsFor s  = [ d | d@(ValD (VarP v) _ _) <- subDecs, v `Set.member` s ]
                    rhs' = addLocals (decsFor usedInRhs) rhs
                    mbG' = case (subGrds, mbG) of
                              ([], Nothing) -> Nothing
                              ([], Just g ) -> Just (addLocals (decsFor usedInGrd) g)
                              (gs, Nothing) -> Just (sAndAll gs)
                              (gs, Just g ) -> Just (sAndAll (gs ++ [addLocals (decsFor usedInGrd) g]))
                in (mbG', rhs')

          pure [CMatch off con (Just ps) mbG rhs allUsed | (mbG, rhs) <- map merge rhss]

  case pat of
    ConP conName _ subpats -> do
      con <- getReference off conName
      flattenAndMerge con (\i -> mkAccessor con i scrut) subpats

    RecP conName []        -> do con <- getReference off conName
                                 pure [CMatch off con Nothing   mbG rhs allUsed | (mbG, rhs) <- rhss]

    WildP                  ->    pure [CWild  off               mbG rhs         | (mbG, rhs) <- rhss]

    -- List cons pattern: y : ys  (InfixP or UInfixP from the parser)
    InfixP p1 conName p2
      | nameBase conName == ":" -> let con = mkName ":" in flattenAndMerge con (\i -> mkAccessorFor (Just BTList) con i scrut) [p1, p2]
    UInfixP p1 conName p2
      | nameBase conName == ":" -> let con = mkName ":" in flattenAndMerge con (\i -> mkAccessorFor (Just BTList) con i scrut) [p1, p2]

    -- Tuple pattern: (a, b, ...)
    TupP subpats -> do
          let n   = length subpats
              con = tupleDataName n
          flattenAndMerge con (\i -> mkAccessorFor (Just (BTTuple n)) con i scrut) subpats

    -- List nil pattern: []
    ListP [] ->        pure [CMatch off (mkName "[]") (Just []) mbG rhs allUsed | (mbG, rhs) <- rhss]

    -- List pattern with elements: [a], [a, b], etc. Desugar to nested cons: a : (b : [])
    ListP ps -> let desugar []     = ListP []
                    desugar (p:rest) = InfixP p (mkName ":") (desugar rest)
                in matchToPair scrut off (Match (desugar ps) grhs locals)

    _ -> fail Unknown $ unlines [ "sCase/pCase: Unsupported pattern:"
                                , "            Saw: " <> pprint pat
                                , ""
                                , "        Only constructors with variables (i.e., Cstr a b _ d)"
                                , "        Empty record matches (i.e., Cstr{})"
                                , "        And wildcards (i.e., _) for default"
                                , "        are supported at the top level."
                                , "        (Integer and string literals are supported in nested positions.)"
                                ]

-- | Flatten a sub-pattern against a given accessor expression.
-- Returns: a simple VarP/WildP for the flat pattern list, a list of
-- synthetic isCstr guard expressions, and let-bindings that bring
-- nested-pattern variables into scope.
flattenPat :: Offset -> Exp -> Pat -> Q (Pat, [Exp], [Dec])
flattenPat _   _   WildP                    = pure (WildP, [], [])
flattenPat _   _   p@(VarP _)               = pure (p,     [], [])
flattenPat off arg (ParensP p)              = flattenPat off arg p
flattenPat off arg (ConP conName _ subpats) = do
  con   <- getReference off conName
  -- Arity check: reify the constructor to find its actual field count
  DataConI _ conType parentName <- reify con
  let arity = countArgs conType
  unless (arity == length subpats) $
    fail off $ unlines [ "sCase/pCase: Arity mismatch in nested pattern."
                       , "        Constructor: " ++ nameBase con
                       , "        Expected   : " ++ show arity
                       , "        Given      : " ++ show (length subpats)
                       ]
  -- Check if the parent type has only one constructor; if so, the tester is trivially true
  singleCon <- isSingleConstructorType parentName
  let tester      = mkTester con arg
      accessor i  = mkAccessor con i arg
  subResults <- zipWithM (flattenPat off . accessor) [(1::Int)..] subpats
  let subGrds = concatMap sndOf3 subResults
      subDecs = concatMap thdOf3 subResults
      subPats = map fstOf3 subResults
      patDecs = [ ValD (VarP v) (NormalB (accessor i)) []
                | (i, VarP v) <- zip [(1::Int)..] subPats ]
      -- Skip the tester guard for single-constructor types (it's always true)
      guards  = (if singleCon then id else (tester :)) (subGrds)
  pure (WildP, guards, patDecs ++ subDecs)
flattenPat off arg (LitP lit) = do
  eq <- litToEq off arg lit
  pure (WildP, [eq], [])
-- Nested list cons pattern: x : xs (InfixP or UInfixP from the parser)
flattenPat off arg (InfixP p1 conName p2)
  | nameBase conName == ":" = flattenCons off arg p1 p2
flattenPat off arg (UInfixP p1 conName p2)
  | nameBase conName == ":" = flattenCons off arg p1 p2
-- Nested empty list pattern: []
flattenPat _   arg (ListP []) =
  pure (WildP, [AppE (VarE 'SL.null) arg], [])
-- Nested list pattern with elements: [a], [a, b], etc. Desugar to nested cons.
flattenPat off arg (ListP (p:ps)) =
  flattenPat off arg (InfixP p (mkName ":") (ListP ps))
-- Nested tuple pattern: (a, b, ...)
flattenPat off arg (TupP pats) = do
  let n = length pats
      accessor i = mkAccessorFor (Just (BTTuple n)) (tupleDataName n) i arg
  subResults <- zipWithM (flattenPat off . accessor) [(1::Int)..] pats
  let subGrds = concatMap sndOf3 subResults
      subDecs = concatMap thdOf3 subResults
      patDecs = [ ValD (VarP v) (NormalB (accessor i)) []
                | (i, VarP v) <- zip [(1::Int)..] (map fstOf3 subResults) ]
  pure (WildP, subGrds, patDecs ++ subDecs)
flattenPat o _ p = fail o $ unlines [ "sCase/pCase: Unsupported complex pattern match."
                                    , "        Saw: " <> pprint p
                                    , ""
                                    , "      Only variables, wildcards, nested constructors, and integer/string literals are supported."
                                    ]

-- | Flatten a nested list cons pattern (x : xs) against an accessor expression.
-- We include a destructuring equality (arg .=== head arg .: tail arg) because lists use
-- SMT Seq, not declare-datatypes, so the solver doesn't automatically know this relationship.
-- This is critical for pCase proof progress; harmless for sCase (redundant guard in ite-chain).
-- NB. For top-level list cons patterns in pCase, the same equality is added by 'processCases'.
flattenCons :: Offset -> Exp -> Pat -> Pat -> Q (Pat, [Exp], [Dec])
flattenCons off arg p1 p2 = do
    let headExpr = mkAccessorFor (Just BTList) (mkName ":") 1 arg
        tailExpr = mkAccessorFor (Just BTList) (mkName ":") 2 arg
        tester   = mkTesterFor (Just BTList) (mkName ":") arg
        destruct = foldl1 AppE [VarE '(.===), arg, InfixE (Just headExpr) (VarE '(SL..:)) (Just tailExpr)]
    sub1 <- flattenPat off headExpr p1
    sub2 <- flattenPat off tailExpr p2
    let subGrds = sndOf3 sub1 ++ sndOf3 sub2
        subDecs = thdOf3 sub1 ++ thdOf3 sub2
        patDecs = [ ValD (VarP v) (NormalB headExpr) [] | VarP v <- [fstOf3 sub1] ]
               ++ [ ValD (VarP v) (NormalB tailExpr) [] | VarP v <- [fstOf3 sub2] ]
    pure (WildP, tester : destruct : subGrds, patDecs ++ subDecs)

-- | Check if a type has only one constructor. Used to skip trivially-true tester guards
-- in nested patterns (e.g., @Just (Pocket n3 n5)@ where @Pocket@ is the sole constructor).
isSingleConstructorType :: Name -> Q Bool
isSingleConstructorType tyName = do
  info <- reify tyName
  pure $ case info of
    TyConI (DataD    _ _ _ _ [_] _) -> True
    TyConI (NewtypeD {})            -> True
    _                               -> False

fstOf3 :: (a, b, c) -> a
fstOf3 (a, _, _) = a

sndOf3 :: (a, b, c) -> b
sndOf3 (_, b, _) = b

thdOf3 :: (a, b, c) -> c
thdOf3 (_, _, c) = c

-- | Get the constructor list for a type. For built-in types, return synthetic entries;
-- for user ADTs, reify via getConstructors.
getCstrs :: Maybe BuiltinType -> String -> Q [(Name, [Type])]
getCstrs (Just bt) _   = pure [(nm, replicate ar WildCardT) | (nm, ar) <- builtinConstructors bt]
getCstrs Nothing   typ = let dropFieldNames (c, nts) = (c, map snd nts)
                          in map dropFieldNames . snd <$> getConstructors (mkName typ)

-- | Validate wildcard placement: unguarded wildcard must be last.
checkWildcard :: String -> Loc -> [Case] -> Q ()
checkWildcard label loc = go
  where go []                         = pure ()
        go (CMatch{}          : rest) = go rest
        go (CWild _ Just{}  _ : rest) = go rest
        go (CWild o Nothing _ : rest) =
              case rest of
                []  -> pure ()
                red -> fail o $ unlines $ (label ++ ": Wildcard makes the remaining matches redundant:")
                                         : ["        " ++ showCaseGen (Just loc) r | r <- red]

-- | Validate that each constructor exists and has the right arity.
checkArities :: String -> String -> [(Name, [Type])] -> [Case] -> Q ()
checkArities label typ cstrs = mapM_ chk1
  where chk1 c = case c of
                    CMatch o nm ps _ _ _ -> isSafe o nm (length <$> ps)
                    CWild  {}            -> pure ()
        isSafe o nm mbLen
          | Just ts <- lookupBase nm cstrs
          = case mbLen of
               Nothing  -> pure ()
               Just cnt -> unless (length ts == cnt)
                                $ fail o $ unlines [ label ++ ": Arity mismatch."
                                                   , "        Type       : " ++ typ
                                                   , "        Constructor: " ++ nameBase nm
                                                   , "        Expected   : " ++ show (length ts)
                                                   , "        Given      : " ++ show cnt
                                                   ]
          | True
          = fail o $ unlines [ label ++ ": Unknown constructor:"
                             , "        Type          : " ++ typ
                             , "        Saw           : " ++ pprint nm
                             , "        Must be one of: " ++ intercalate ", " (map (pprint . fst) cstrs)
                             ]

-- * sCase

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
              mbt      = recognizeBuiltin typ
          case metaParse fullCase of
            Right (CaseE scrut matches) -> do
              mbFnName <- case mbt of
                Just BTList      -> pure (Just (VarE 'SL.list))
                Just BTMaybe     -> pure (Just (VarE 'SM.sCaseMaybe))
                Just BTEither    -> pure (Just (VarE 'SE.sCaseEither))
                Just (BTTuple _) -> pure Nothing
                Nothing -> lookupValueName fnTok >>= \case
                  Just n  -> pure (Just (VarE n))
                  Nothing -> fail Unknown $ unlines [ "sCase: Unknown symbolic ADT: " <> typ
                                                    , ""
                                                    , "        To use a symbolic case expression, declare your ADT, and then:"
                                                    , "             mkSymbolic [''" <> typ <> "]"
                                                    , "        In a template-haskell context."
                                                    ]
              cases <- zipWithM (matchToPair scrut) (offsets ++ repeat Unknown) matches >>= checkCase scrut typ mbt . concat
              buildCase typ mbFnName scrut cases
            Right _  -> fail Unknown "sCase: Parse error, cannot extract a case-expression."
            Left err -> case lines err of
                          (_:loc:res) | ["SrcLoc", _, l, c] <- words loc, all isDigit l, all isDigit c
                             -> fail (OffBy (read l - 1) (read c - 1) 1) (unlines res)
                          _  -> fail Unknown $ "sCase parse error: " <> err

    buildCase _    (Just caseFunc) scrut (Left  cases) = pure $ AppE (foldl AppE caseFunc cases) scrut
    buildCase _    Nothing         _     (Left  _)     = error "sCase: impossible: Strategy A without case function"
    buildCase typ  _               _scrut (Right cases) = do
        uniq <- newName "u"
        let suffix = drop 2 (show uniq)
            fallback  = AppE (VarE 'sym) (LitE (StringL ("unmatched_sCase_" ++ typ ++ "_" ++ suffix)))
            -- NB. Do NOT optimize the single-element case [(_, e)] to skip the guard.
            -- The ite-chain may not cover all constructors (e.g., guarded matches with
            -- a wildcard fallback), so the unmatched fallback must remain reachable.
            iteChain []              = pure fallback
            iteChain ((t, e) : rest) = do r <- iteChain rest
                                          pure $ foldl AppE (VarE 'ite) [t, e, r]
        iteChain cases

    -- Make sure things are in good-shape and decide if we have guards
    checkCase :: Exp -> String -> Maybe BuiltinType -> [Case] -> Q (Either [Exp] [(Exp, Exp)])
    checkCase scrut typ mbt cases = do
        loc   <- location
        cstrs <- getCstrs mbt typ

        -- Is there a catch all clause?
        let hasCatchAll = or [True | CWild _ Nothing _ <- cases]

        checkWildcard "sCase" loc cases
        checkArities  "sCase" typ cstrs cases

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
            chk2 _ [] = pure ()

            -- If we have a non-guarded match, then there must be no matches for this constructor later on. If so, they're redundant.
            chk2 seen (c@(CMatch _ nm _ Nothing _ _) : rest)
              = case filter (\oc -> maybe False (sameBase nm) (getCaseConstructor oc)) rest of
                  [] -> chk2 (Set.insert (nameBase nm) seen) rest
                  os -> overlap (last os) (c : init os)

            -- If we have a guarded match, then this guard can fail. So either there must be a match
            -- for it later on, or there must be a catch-all. We also accept it if the same constructor
            -- was seen earlier (e.g., multiple nested-pattern alternatives like Left (x:_) / Left []).
            chk2 seen (c@(CMatch _ nm _ Just{} _ _) : rest)
              | hasCatchAll || any (\oc -> maybe False (sameBase nm) (getCaseConstructor oc)) rest || nameBase nm `Set.member` seen
              = chk2 (Set.insert (nameBase nm) seen) rest
              | True
              = unmatched c

            -- If there's a guarded wildcard, must make sure there's a catch all afterwards
            chk2 seen (c@(CWild _ Just{} _) : rest)
              | hasCatchAll
              = chk2 seen rest
              | True
              = unmatched c

            -- No need to worry about anything following catch-all, since we already covered that before
            chk2 seen (CWild _ Nothing _ : rest) = chk2 seen rest

        chk2 Set.empty cases

        -- At this point, we either have a simple case with no guards, in which case
        -- we translate this to an sCase for that type. So find all alternatives.
        -- Otherwise, this will become an ite-chain.
        -- Tuples don't have a case analyzer function, so we always use the ite-chain path for them.
        -- Other built-in types (Maybe, Either, List) now have case analyzers and can use Strategy A.
        let hasGuards    = any isGuarded cases
            isTuple      = case mbt of { Just (BTTuple _) -> True; _ -> False }
            useIteChain  = hasGuards || isTuple

        if not useIteChain
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
                                           CMatch _ nm _ _ _ _ -> sameBase nm w
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
                         where matches cstr c | Just n <- getCaseConstructor c, sameBase n cstr = [c]
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
                           case lookupBase nm cstrs of
                             Nothing -> fail o $ unlines [ "sCase: Impossible happened."
                                                         , "        Unable to determine params for: " <> pprint nm
                                                         ]
                             Just ts -> do let pats = fromMaybe (map (const WildP) ts) mbp
                                               args = [mkAccessorFor mbt nm i scrut | (i, _) <- zip [(1 :: Int) ..] ts]
                                               testerExpr = mkTesterFor mbt nm scrut

                                               -- What are the free variables in the guard and the rhs that we bind?
                                               used    = Set.fromList [n | VarP n <- pats] `Set.intersection` allUsed
                                               close e = foldr1 (AppE . AppE (VarE 'const)) (e:extras)
                                                 where extras = map VarE $ Set.toList (used Set.\\ freeVars e)

                                               mkApp f | null pats = f
                                                       | True      = foldl AppE (LamE pats f) args

                                               grd :: Exp
                                               grd = case mbG of
                                                       Nothing -> testerExpr
                                                       Just g  -> sAndAll [testerExpr, mkApp (close g)]

                                           pure (grd, mkApp (close rhs))

                   Right <$> mapM collect cases

-- * pCase

-- | Quasi-quoter for proof case-splits.
--
-- Like 'sCase', but generates @cases [cond ==> proof, ...]@ instead of
-- @ite@ chains. Wildcards are allowed as the last scrutinee (with or
-- without guards), and exhaustiveness is checked at proof time by the
-- @cases@ combinator rather than at compile time.
--
-- Guards within the same constructor accumulate negations: a second guard
-- implicitly assumes the first guard failed. A wildcard guard is the
-- negation of the disjunction of all prior guards (De Morgan).
pCase :: QuasiQuoter
pCase = QuasiQuoter
  { quoteExp  = extractProof
  , quotePat  = bad "pattern"
  , quoteType = bad "type"
  , quoteDec  = bad "declaration"
  }
  where
    bad ctx _ = fail Unknown $ "pCase: not usable in " <> ctx <> " context"

    extractProof :: String -> ExpQ
    extractProof src =
      case parts src of
        Nothing -> fail Unknown $ unlines [ "pCase: Failed to parse a proof case-expression."
                                          , ""
                                          , "           Instead of:   case      expr of alts"
                                          , "           Write     : [pCase|Type expr of alts|]"
                                          , ""
                                          , "        where Type is the underlying concrete type of the expression."
                                          ]
        Just ((typ, scrutStr), altsStr) -> do
          let fullCase = "case " <> scrutStr <> " of " <> altsStr
              offsets  = findOffsets src
              mbt      = recognizeBuiltin typ
          case metaParse fullCase of
            Right (CaseE scrut matches) -> do
              cs <- zipWithM (matchToPair scrut) (offsets ++ repeat Unknown) matches
              validated <- checkProofCase typ mbt (concat cs)
              buildProofCase scrut typ mbt validated
            Right _  -> fail Unknown "pCase: Parse error, cannot extract a case-expression."
            Left err -> case lines err of
                          (_:loc:res) | ["SrcLoc", _, l, c] <- words loc, all isDigit l, all isDigit c
                             -> fail (OffBy (read l - 1) (read c - 1) 1) (unlines res)
                          _  -> fail Unknown $ "pCase parse error: " <> err

    -- | Validate cases for proof context
    checkProofCase :: String -> Maybe BuiltinType -> [Case] -> Q [Case]
    checkProofCase typ mbt cases = do
        loc <- location
        cstrs <- getCstrs mbt typ

        checkWildcard "pCase" loc cases
        checkArities  "pCase" typ cstrs cases

        -- Wildcards must come after all explicit constructor matches
        let checkWildBeforeCstr [] = pure ()
            checkWildBeforeCstr (CWild o _ _ : rest)
              | any (\case CMatch{} -> True; _ -> False) rest
              = fail o $ unlines $ "pCase: Wildcard must come after all constructor matches:"
                                 : ["        " ++ showCaseGen (Just loc) r | r <- filter (\case CMatch{} -> True; _ -> False) rest]
            checkWildBeforeCstr (_ : rest) = checkWildBeforeCstr rest
        checkWildBeforeCstr cases

        -- Check overlap: unguarded constructor match followed by same constructor
        let chk2 [] = pure ()
            chk2 (c@(CMatch _ nm _ Nothing _ _) : rest)
              = case filter (\oc -> maybe False (sameBase nm) (getCaseConstructor oc)) rest of
                  [] -> chk2 rest
                  os -> overlap loc (last os) (c : init os)
            chk2 (_ : rest) = chk2 rest

        chk2 cases

        -- If every constructor has an unguarded match, any wildcard is redundant
        let fullyCovered = [ cstr | (cstr, _) <- cstrs
                                  , any (\c -> maybe False (sameBase cstr) (getCaseConstructor c) && not (isGuarded c)) cases
                                  ]
        case [c | c@CWild{} <- cases] of
          []    -> pure ()
          (c:_) | length fullyCovered == length cstrs
                -> fail (caseOffset c) "pCase: Wildcard match is redundant"
                | True
                -> pure ()

        -- No exhaustiveness check: the `cases` combinator checks completeness at proof time.
        pure cases

    overlap loc x xs = fail (caseOffset x) $ unlines $ [ "pCase: Overlapping case constructors:"
                                                        , "        Constructor: " ++ showCase x
                                                        ]
                                                     ++ [ "      Overlaps with:" ]
                                                     ++ [ "        " ++ showCaseGen (Just loc) p | p <- xs]

    -- | Build the proof case expression
    buildProofCase :: Exp -> String -> Maybe BuiltinType -> [Case] -> ExpQ
    buildProofCase scrut typ mbt cases = do
        cstrs <- getCstrs mbt typ
        -- Collect guard variables for each constructor across all arms
        -- (needed to suppress false "unused binding" warnings for guard-only variables)
        let allGrdVars :: Map Name (Set Name)
            allGrdVars = Map.fromListWith Set.union
                           [ (nm, maybe Set.empty freeVars mbG)
                           | CMatch _ nm _ mbG _ _ <- cases ]
        allPairs <- processCases scrut cstrs mbt allGrdVars [] cases
        let casesName   = mkName "cases"
            impliesName = mkName "==>"
            mkPair (g, r) = InfixE (Just g) (VarE impliesName) (Just r)
        pure $ AppE (VarE casesName) (ListE (map mkPair allPairs))

    -- | Process all cases linearly, accumulating prior guards.
    -- Prior guards are tagged with their constructor name (Nothing for wildcards).
    -- Each entry stores (constructor, fullGuard, userGuardOnly):
    --   fullGuard    = the complete guard expression (used for wildcard De Morgan negation)
    --   userGuardOnly = Just the user guard part (used for same-constructor negation)
    --                   Nothing if unguarded (same-constructor arms don't negate unguarded matches)
    processCases :: Exp -> [(Name, [Type])] -> Maybe BuiltinType -> Map Name (Set Name) -> [(Maybe Name, Exp, Maybe Exp)] -> [Case] -> Q [(Exp, Exp)]
    processCases _     _     _   _          _           []         = pure []
    processCases scrut cstrs mbt allGrdVars priorGuards (c:rest) = case c of
      CWild _ mbG rhs -> do
        -- Wildcard: negate the disjunction of ALL prior full guards (De Morgan)
        let allGuards  = [g | (_, g, _) <- priorGuards]
            baseGuard  = negateAll allGuards
            finalGuard = case mbG of
                           Nothing -> baseGuard
                           Just g  -> sAndAll [baseGuard, g]
        rest' <- processCases scrut cstrs mbt allGrdVars (priorGuards ++ [(Nothing, finalGuard, Nothing)]) rest
        pure $ (finalGuard, rhs) : rest'

      CMatch _o nm mbp mbG rhs _allUsed -> do
        let ts   = case lookupBase nm cstrs of
                     Just t  -> t
                     Nothing -> error $ "pCase: impossible: unknown constructor " ++ nameBase nm
            pats = fromMaybe (map (const WildP) ts) mbp

            -- Build let-bindings for pattern variables
            args    = [(i, mkAccessorFor mbt nm i scrut) | (i, _) <- zip [(1 :: Int) ..] ts]
            bindings = [ ValD (VarP v) (NormalB acc) []
                       | (i, acc) <- args, VarP v <- [pats !! (i - 1)] ]

            testerGuard = mkTesterFor mbt nm scrut

            -- For list cons patterns in pCase, add a destructuring equality:
            --   scrut .=== head scrut .: tail scrut
            -- Lists use SMT Seq (not declare-datatypes), so the solver doesn't automatically
            -- know that xs = head xs .: tail xs from sNot (null xs). We must add an explicit
            -- equality to give the solver this information, mirroring what 'split' does.
            -- All other types (ADTs, Maybe, Either, Tuple) use declare-datatypes and get
            -- these axioms for free.
            -- NB. For nested list cons patterns, the same equality is added by 'flattenCons'.
            destructEq
              | Just BTList <- mbt, nameBase nm == ":"
              = let hd = AppE (VarE 'SL.head) scrut
                    tl = AppE (VarE 'SL.tail) scrut
                in [foldl1 AppE [VarE '(.===), scrut, InfixE (Just hd) (VarE '(SL..:)) (Just tl)]]
              | otherwise
              = []

            -- Only negate prior USER guards for the SAME constructor (others are mutually exclusive)
            sameUserGuards = [ ug | (Just cn, _, Just ug) <- priorGuards, sameBase cn nm ]
            negPriors      = map (AppE (VarE 'sNot)) sameUserGuards

            -- Build the final guard (wrap user guard in bindings so pattern vars are in scope)
            grdVars     = maybe Set.empty freeVars mbG
            grdBindings = filter (\case
                                     ValD (VarP v) _ _ -> v `Set.member` grdVars
                                     _                 -> True) bindings
            guardParts  = [testerGuard] ++ destructEq ++ negPriors ++ maybe [] (pure . addLocals grdBindings) mbG
            finalGuard  = sAndAll guardParts

            -- Wrap RHS with let-bindings; include all bindings except those
            -- used in any guard of the same constructor but not in this RHS
            -- (to avoid false "unused" warnings from GHC for guard-only variables)
            cstrGrdVars = Map.findWithDefault Set.empty nm allGrdVars
            rhsVars = freeVars rhs
            rhs'    = addLocals (filter (\case
                                            ValD (VarP v) _ _ -> not (v `Set.member` cstrGrdVars) || v `Set.member` rhsVars
                                            _                 -> True) bindings) rhs

            -- Track: full guard for wildcard negation, user guard for same-constructor negation
            userGuardOnly = case mbG of
                              Just g  -> Just (addLocals grdBindings g)
                              Nothing -> Nothing
            priorGuards' = priorGuards ++ [(Just nm, finalGuard, userGuardOnly)]

        rest' <- processCases scrut cstrs mbt allGrdVars priorGuards' rest
        pure $ (finalGuard, rhs') : rest'

    -- | Negate the disjunction of all given guards using De Morgan: sNot (g1 .|| g2 .|| ...)
    negateAll :: [Exp] -> Exp
    negateAll [] = VarE 'sTrue
    negateAll gs = AppE (VarE 'sNot) (foldl1 (\a b -> foldl1 AppE [VarE '(.||), a, b]) gs)

-- * Standalone helpers

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

-- | Count the number of arguments in a constructor type by counting arrows.
-- e.g., @Integer -> String -> Bool@ has 2 arguments.
-- Handles both plain ArrowT and multiplicity-annotated arrows (MulArrowT).
countArgs :: Type -> Int
countArgs (AppT (AppT ArrowT _) rest)            = 1 + countArgs rest
countArgs (AppT (AppT (AppT MulArrowT _) _) rest) = 1 + countArgs rest
countArgs (ForallT _ _ t)                         = countArgs t
countArgs _                                       = 0

-- | Generate a symbolic equality guard for a literal pattern.
-- @litToEq off arg lit@ produces the expression @arg .== litVal@.
-- For integers, the literal is used directly (relying on @fromInteger@).
-- For strings, the literal is wrapped with @literal@ to convert @String@ to @SString@.
-- Only integer and string literals are supported; others produce a compile error.
litToEq :: Offset -> Exp -> Lit -> Q Exp
litToEq _   arg (IntegerL n) = pure $ foldl1 AppE [VarE '(.==), arg, LitE (IntegerL n)]
litToEq _   arg (StringL  s) = pure $ foldl1 AppE [VarE '(.==), arg, AppE (VarE 'literal) (LitE (StringL s))]
litToEq off _   lit          = fail off $ unlines
  [ "sCase/pCase: Unsupported literal in pattern: " ++ show lit
  , "       Only integer and string literals are supported."
  ]
