-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.SMT.SMTLib2
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Conversion of symbolic programs to SMTLib format, Using v2 of the standard
-----------------------------------------------------------------------------

{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.SMT.SMTLib2(cvt, cvtExp, cvtCV, cvtInc, declUserFuns, constructTables, setSMTOption) where

import Crypto.Hash.SHA512 (hash)
import qualified Data.ByteString.Base16 as B
import qualified Data.ByteString.Char8  as BC

import Data.Bits  (bit)
import Data.List  (intercalate, partition, nub, elemIndex)
import Data.Maybe (listToMaybe, catMaybes)

import qualified Data.Foldable as F (toList)
import qualified Data.Map.Strict      as M
import qualified Data.IntMap.Strict   as IM
import           Data.Set             (Set)
import qualified Data.Set             as Set

import Data.SBV.Core.Data
import Data.SBV.Core.Kind (smtType, needsFlattening)
import Data.SBV.SMT.Utils
import Data.SBV.Control.Types

import Data.SBV.Core.Symbolic ( QueryContext(..), SetOp(..), getUserName', getSV, regExpToSMTString
                              , SMTDef(..), ResultInp(..), ProgInfo(..), SpecialRelOp(..), SMTLambda(..)
                              )

import Data.SBV.Utils.PrettyNum (smtRoundingMode, cvToSMTLib)

import qualified Data.Generics.Uniplate.Data as G

import qualified Data.Graph as DG

-- | For higher-order functions, we firstify them. This requires a uniqu name creation. Here,
-- we create a firstified name based on the operation. The suffix appended will have at most uniqLen length.
firstify :: Int -> Op -> String
firstify uniqLen o = prefix o ++ "_" ++ take uniqLen (BC.unpack (B.encode (hash (BC.pack (compress (show o))))))
  where prefix (SeqOp SBVReverse {}) = "sbv.reverse"
        prefix (SeqOp SBVZip     {}) = "sbv.zip"
        prefix (SeqOp SBVZipWith {}) = "sbv.zipWith"
        prefix (SeqOp SBVMap     {}) = "sbv.map"
        prefix (SeqOp SBVFoldl   {}) = "sbv.foldl"
        prefix (SeqOp SBVFoldr   {}) = "sbv.foldr"
        prefix (SeqOp SBVFilter  {}) = "sbv.filter"
        prefix (SeqOp SBVAll     {}) = "sbv.all"
        prefix (SeqOp SBVAny     {}) = "sbv.any"
        prefix (SeqOp SBVConcat  {}) = "sbv.concat"
        prefix _                     = error $ unlines [ "***"
                                                       , "*** Data.SBV.firstify: Didn't expect firstification to be called."
                                                       , "***"
                                                       , "***   Operator: " ++ show o
                                                       , "***"
                                                       , "*** Please report this as a bug."
                                                       ]

        -- compress and make spaces uniform; get words, and then unwords
        compress = unwords . words

-- | Translate a problem into an SMTLib2 script
cvt :: SMTLibConverter ([String], [String])
cvt ctx curProgInfo kindInfo isSat comments allInputs (_, consts) tbls uis defs (SBVPgm asgnsSeq) cstrs out cfg = (pgm, exportedDefs)
  where allKinds       = Set.toList kindInfo

        hasInteger     = KUnbounded `Set.member` kindInfo
        hasArrays      = not (null [() | KArray{}     <- allKinds])
        hasNonBVArrays = not (null [() | KArray k1 k2 <- allKinds, not (isBounded k1 && isBounded k2)])
        hasReal        = KReal      `Set.member` kindInfo
        hasFP          =  not (null [() | KFP{} <- allKinds])
                       || KFloat     `Set.member` kindInfo
                       || KDouble    `Set.member` kindInfo
        hasString      = KString     `Set.member` kindInfo
        hasRegExp      = (not . null) [() | (_ :: RegExOp) <- G.universeBi asgnsSeq]
        hasChar        = KChar      `Set.member` kindInfo
        hasRounding    = not $ null [s | (s, _) <- usorts, s == "RoundingMode"]
        hasBVs         = not (null [() | KBounded{} <- allKinds])
        usorts         = [(s, dt) | KUserSort s dt <- allKinds]
        trueUSorts     = [s | (s, _) <- usorts, s /= "RoundingMode"]
        tupleArities   = findTupleArities kindInfo
        hasOverflows   = (not . null) [() | (_ :: OvOp) <- G.universeBi asgnsSeq]
        hasQuantBools  = (not . null) [() | QuantifiedBool{} <- G.universeBi asgnsSeq]
        hasList        = any isList kindInfo
        hasSets        = any isSet kindInfo
        hasTuples      = not . null $ tupleArities
        hasEither      = any isEither kindInfo
        hasMaybe       = any isMaybe  kindInfo
        hasRational    = any isRational kindInfo
        rm             = roundingMode cfg
        solverCaps     = capabilities (solver cfg)
        hasLambdas     = let needsLambda SBVZipWith{} = True
                             needsLambda SBVMap{}     = True
                             needsLambda SBVFoldl{}   = True
                             needsLambda SBVFoldr{}   = True
                             needsLambda SBVFilter{}  = True
                             needsLambda SBVAll{}     = True
                             needsLambda SBVAny{}     = True
                             needsLambda _            = False
                         in (not . null) [ () | o :: SeqOp <- G.universeBi asgnsSeq, needsLambda o]

        (needsQuantifiers, needsSpecialRels, specialFuncs) = case curProgInfo of
           ProgInfo hasQ srs tcs sf -> (hasQ, not (null srs && null tcs), sf)

        -- Is there a reason why we can't handle this problem?
        -- NB. There's probably a lot more checking we can do here, but this is a start:
        doesntHandle = listToMaybe [nope w | (w, have, need) <- checks, need && not (have solverCaps)]
           where checks = [ ("data types",             supportsDataTypes,          hasTuples || hasEither || hasMaybe)
                          , ("needs lambdas",          supportsLambdas,            hasLambdas)
                          , ("set operations",         supportsSets,               hasSets)
                          , ("bit vectors",            supportsBitVectors,         hasBVs)
                          , ("special relations",      supportsSpecialRels,        needsSpecialRels)
                          , ("needs quantifiers",      supportsQuantifiers,        needsQuantifiers)
                          , ("unbounded integers",     supportsUnboundedInts,      hasInteger)
                          , ("algebraic reals",        supportsReals,              hasReal)
                          , ("floating-point numbers", supportsIEEE754,            hasFP)
                          , ("uninterpreted sorts",    supportsUninterpretedSorts, not (null trueUSorts))
                          ]

                 nope w = [ "***     Given problem requires support for " ++ w
                          , "***     But the chosen solver (" ++ show (name (solver cfg)) ++ ") doesn't support this feature."
                          ]

        -- Some cases require all, some require none. Sigh.. Also, if there're lambdas CVC5 needs HO_ALL
        setAll reason = ["(set-logic " ++ allName ++ ") ; "  ++ reason ++ ", using catch-all."]
          where allName | hasLambdas && isCVC5 = "HO_ALL"
                        | True                 = "ALL"

                isCVC5 = case name (solver cfg) of
                           CVC5 -> True
                           _    -> False

        -- Determining the logic is surprisingly tricky!
        logic
           -- user told us what to do: so just take it:
           | Just l <- case [l | SetLogic l <- solverSetOptions cfg] of
                         []  -> Nothing
                         [l] -> Just l
                         ls  -> error $ unlines [ ""
                                                , "*** Only one setOption call to 'setLogic' is allowed, found: " ++ show (length ls)
                                                , "***  " ++ unwords (map show ls)
                                                ]
           = case l of
               Logic_NONE -> ["; NB. Not setting the logic per user request of Logic_NONE"]
               _          -> ["(set-logic " ++ show l ++ ") ; NB. User specified."]

           -- There's a reason why we can't handle this problem:
           | Just cantDo <- doesntHandle
           = error $ unlines $   [ ""
                                 , "*** SBV is unable to choose a proper solver configuration:"
                                 , "***"
                                 ]
                             ++ cantDo
                             ++ [ "***"
                                , "*** Please report this as a feature request, either for SBV or the backend solver."
                                ]

           -- Otherwise, we try to determine the most suitable logic.
           -- NB. This isn't really fool proof!

           -- we never set QF_S (ALL seems to work better in all cases)

           | needsSpecialRels      = ["; has special relations, no logic set."]

           -- Things that require ALL
           | hasLambdas            = setAll "has lambda expressions"
           | hasInteger            = setAll "has unbounded values"
           | hasRational           = setAll "has rational values"
           | hasReal               = setAll "has algebraic reals"
           | not (null trueUSorts) = setAll "has user-defined sorts"
           | hasNonBVArrays        = setAll "has non-bitvector arrays"
           | hasTuples             = setAll "has tuples"
           | hasEither             = setAll "has either type"
           | hasMaybe              = setAll "has maybe type"
           | hasSets               = setAll "has sets"
           | hasList               = setAll "has lists"
           | hasChar               = setAll "has chars"
           | hasString             = setAll "has strings"
           | hasRegExp             = setAll "has regular expressions"
           | hasOverflows          = setAll "has overflow checks"
           | hasQuantBools         = setAll "has quantified booleans"

           | hasFP || hasRounding
           = if needsQuantifiers
             then ["(set-logic ALL)"]
             else if hasBVs
                  then ["(set-logic QF_FPBV)"]
                  else ["(set-logic QF_FP)"]

           -- If we're in a user query context, we'll pick ALL, otherwise
           -- we'll stick to some bit-vector logic based on what we see in the problem.
           -- This is controversial, but seems to work well in practice.
           | True
           = case ctx of
               QueryExternal -> ["(set-logic ALL) ; external query, using all logics."]
               QueryInternal -> if supportsBitVectors solverCaps
                                then ["(set-logic " ++ qs ++ as ++ ufs ++ "BV)"]
                                else ["(set-logic ALL)"] -- fall-thru
          where qs  | not needsQuantifiers  = "QF_"
                    | True                  = ""
                as  | not hasArrays         = ""
                    | True                  = "A"
                ufs | null uis && null tbls = ""     -- we represent tables as UFs
                    | True                  = "UF"

        -- SBV always requires the production of models!
        getModels   = "(set-option :produce-models true)"
                    : concat [flattenConfig | any needsFlattening kindInfo, Just flattenConfig <- [supportsFlattenedModels solverCaps]]

        -- process all other settings we're given. If an option cannot be repeated, we only take the last one.
        userSettings = map (setSMTOption cfg) $ filter (not . isLogic) $ foldr comb [] $ solverSetOptions cfg
           where -- Logic is already processed, so drop it:
                 isLogic SetLogic{} = True
                 isLogic _          = False

                 -- SBV sets diagnostic-output channel on some solvers. If the user also gives it, let's just
                 -- take it by only taking the last one
                 isDiagOutput DiagnosticOutputChannel{} = True
                 isDiagOutput _                         = False

                 comb o rest
                   | isDiagOutput o && any isDiagOutput rest =     rest
                   | True                                    = o : rest

        settings =  userSettings        -- NB. Make sure this comes first!
                 ++ getModels
                 ++ logic

        (inputs, trackerVars)
            = case allInputs of
                ResultTopInps ists -> ists
                ResultLamInps ps   -> error $ unlines [ ""
                                                      , "*** Data.SBV.smtLib2: Unexpected lambda inputs in conversion"
                                                      , "***"
                                                      , "*** Saw: " ++ show ps
                                                      ]

        pgm  =  map ("; " ++) comments
             ++ settings
             ++ [ "; --- uninterpreted sorts ---" ]
             ++ concatMap declSort usorts
             ++ [ "; --- tuples ---" ]
             ++ concatMap declTuple tupleArities
             ++ [ "; --- sums ---" ]
             ++ (if containsSum       kindInfo then declSum       else [])
             ++ (if containsMaybe     kindInfo then declMaybe     else [])
             ++ (if containsRationals kindInfo then declRationals else [])
             ++ [ "; --- literal constants ---" ]
             ++ concatMap (declConst cfg) consts
             ++ [ "; --- top level inputs ---"]
             ++ concat [declareFun s (SBVType [kindOf s]) (userName s) | var <- inputs, let s = getSV var]
             ++ [ "; --- optimization tracker variables ---" | not (null trackerVars) ]
             ++ concat [declareFun s (SBVType [kindOf s]) (Just ("tracks " <> nm)) | var <- trackerVars, let s = getSV var, let nm = getUserName' var]
             ++ [ "; --- constant tables ---" ]
             ++ concatMap (uncurry (:) . mkTable) constTables
             ++ [ "; --- non-constant tables ---" ]
             ++ map nonConstTable nonConstTables
             ++ [ "; --- uninterpreted constants ---" ]
             ++ concatMap (declUI curProgInfo) uis
             ++ [ "; --- Firstified function definitions" | not (null specialFuncs) ]
             ++ concat firstifiedDefs
             ++ [ "; --- Firstified equivalences"         | not (null exportedFirstifiedEqualities) ]
             ++ concat exportedFirstifiedEqualities
             ++ [ "; -- NB. Skipping firstified equivalences, due to generateHOEquivs setting." | not (null firstifiedEqualities || generateHOEquivs)]
             ++ [ "; --- user defined functions ---"]
             ++ userDefs
             ++ [ "; --- assignments ---" ]
             ++ concatMap (declDef curProgInfo cfg tableMap) asgns
             ++ [ "; --- delayedEqualities ---" ]
             ++ map (\s -> "(assert " ++ s ++ ")") delayedEqualities
             ++ [ "; --- formula ---" ]
             ++ finalAssert

        SMTConfig{generateHOEquivs, kdOptions = KDOptions{firstifyUniqueLen}} = cfg

        (firstifiedDefs, firstifiedFuncs)
           = case dup res of
               Nothing         -> ([def | (_, (_, def)) <- res], [(op, nm) | (op, (nm, _)) <- res])
               Just (o, o', n) -> error $ unlines [ ""
                                                  , "*** Data.SBV: Insufficient unique length in firstification."
                                                  , "***"
                                                  , "***   Operator 1 : " ++ show o
                                                  , "***   Operator 2 : " ++ show o'
                                                  , "***   Mapped name: " ++ n
                                                  , "***   Unique len : " ++ show firstifyUniqueLen
                                                  , "***"
                                                  , "*** Such collisions should be rare, but looks like you ran into one!"
                                                  , "*** Try running with an increased unique-length:"
                                                  , "***"
                                                  , "***     solver{firstifyUniqueLen = N}"
                                                  , "***"
                                                  , "*** where N is larger than " ++ show firstifyUniqueLen
                                                  , "***"
                                                  , "*** For instance:"
                                                  , "***"
                                                  , "***     satWith z3{firstUniqueLen = " ++ show (firstifyUniqueLen + 1) ++ "}"
                                                  , "***"
                                                  , "*** If that doesn't resolve the problem, or if you believe this is caused by some"
                                                  , "*** other problem, please report his as a bug."
                                                  ]
           where res = [(op, declSBVFunc cfg op) | op <- reverse specialFuncs]
                 dup []                = Nothing
                 dup ((o, (n, _)): xs) = case [o' | (o', (n', _)) <- xs, n == n'] of
                                           []       -> dup xs
                                           (o' : _) -> Just (o, o', n)

        exportedFirstifiedEqualities
           | generateHOEquivs
           = firstifiedEqualities
           | True
           = []

        firstifiedEqualities = map equate $ combs firstifiedFuncs
           where combs :: [(Op, String)] -> [(Op, (String, SMTLambda), (String, SMTLambda))]
                 combs []             = []
                 combs ((o1, nm1):fs) = [(o1, (nm1, l1), (nm2, l2)) | (o2, nm2) <- fs, Just (l1, l2) <- [getFuncs o1 o2]] ++ combs fs

                 -- same if the same op sans the lambda
                 getFuncs :: Op -> Op -> Maybe (SMTLambda, SMTLambda)
                 getFuncs (SeqOp (SBVZipWith a b c f)) (SeqOp (SBVZipWith x y z g)) | [a, b, c] == [x, y, z] = Just (f, g)
                 getFuncs (SeqOp (SBVMap     a b   f)) (SeqOp (SBVMap     x y   g)) | [a, b   ] == [x, y   ] = Just (f, g)
                 getFuncs (SeqOp (SBVFoldl   a b   f)) (SeqOp (SBVFoldl   x y   g)) | [a, b   ] == [x, y   ] = Just (f, g)
                 getFuncs (SeqOp (SBVFoldr   a b   f)) (SeqOp (SBVFoldr   x y   g)) | [a, b   ] == [x, y   ] = Just (f, g)
                 getFuncs (SeqOp (SBVFilter  a     f)) (SeqOp (SBVFilter  x     g)) | [a      ] == [x      ] = Just (f, g)
                 getFuncs (SeqOp (SBVAll     a     f)) (SeqOp (SBVAll     x     g)) | [a      ] == [x      ] = Just (f, g)
                 getFuncs (SeqOp (SBVAny     a     f)) (SeqOp (SBVAny     x     g)) | [a      ] == [x      ] = Just (f, g)
                 getFuncs _                            _                                                     = Nothing

                 equate :: (Op, (String, SMTLambda), (String, SMTLambda)) -> [String]
                 equate (o, (nm1, f), (nm2, g)) = [ "; Equality for " ++ nm1 ++ " vs. " ++ nm2
                                                  , "(assert (forall (" ++ decls ++ ")"
                                                  , "                (=> (= " ++ show f ++ " " ++ show g ++ ")"
                                                  , "                    (= (" ++ nm1 ++ " " ++ args ++ ") (" ++ nm2 ++ " " ++ args ++ ")))))"
                                                  ]
                      where params = paramsOf o
                            args   = unwords $ map fst params
                            decls  = unwords ['(' : n ++ " " ++ smtType k ++ ")" | (n, k) <- params]

                            paramsOf (SeqOp (SBVZipWith k1 k2 _ _)) = [           ("xs", KList k1), ("ys", KList k2)]
                            paramsOf (SeqOp (SBVMap     k1    _ _)) = [           ("xs", KList k1)]
                            paramsOf (SeqOp (SBVFoldl   k1 k2   _)) = [("b", k2), ("xs", KList k1)]
                            paramsOf (SeqOp (SBVFoldr   k1 k2   _)) = [("b", k2), ("xs", KList k1)]
                            paramsOf (SeqOp (SBVFilter  k1      _)) = [           ("xs", KList k1)]
                            paramsOf (SeqOp (SBVAll     k1      _)) = [           ("xs", KList k1)]
                            paramsOf (SeqOp (SBVAny     k1      _)) = [           ("xs", KList k1)]
                            paramsOf op                             = error $ "Data.SBV.firstifiedEqualities: Unexpected op: " ++ show op

        userDefs = declUserFuns defs
        exportedDefs
          | null userDefs
          = ["; No calls to 'smtFunction' found."]
          | True
          = "; Automatically generated by SBV. Do not modify!" : userDefs


        (tableMap, constTables, nonConstTables) = constructTables rm consts tbls

        delayedEqualities = concatMap snd nonConstTables

        finalAssert
          | noConstraints = []
          | True          =    map (\(attr, v) -> "(assert "      ++ addAnnotations attr (mkLiteral v) ++ ")") hardAsserts
                            ++ map (\(attr, v) -> "(assert-soft " ++ addAnnotations attr (mkLiteral v) ++ ")") softAsserts
          where mkLiteral (Left  v) =            cvtSV v
                mkLiteral (Right v) = "(not " ++ cvtSV v ++ ")"

                (noConstraints, assertions) = finalAssertions

                hardAsserts, softAsserts :: [([(String, String)], Either SV SV)]
                hardAsserts = [(attr, v) | (False, attr, v) <- assertions]
                softAsserts = [(attr, v) | (True,  attr, v) <- assertions]

        finalAssertions :: (Bool, [(Bool, [(String, String)], Either SV SV)])  -- If Left: positive, Right: negative
        finalAssertions
           | null finals = (True,  [(False, [], Left trueSV)])
           | True        = (False, finals)

           where finals  = cstrs' ++ maybe [] (\r -> [(False, [], r)]) mbO

                 cstrs' =  [(isSoft, attrs, c') | (isSoft, attrs, c) <- F.toList cstrs, Just c' <- [pos c]]

                 mbO | isSat = pos out
                     | True  = neg out

                 neg s
                  | s == falseSV = Nothing
                  | s == trueSV  = Just $ Left falseSV
                  | True         = Just $ Right s

                 pos s
                  | s == trueSV  = Nothing
                  | s == falseSV = Just $ Left falseSV
                  | True         = Just $ Left s

        asgns = F.toList asgnsSeq

        userNameMap = M.fromList $ map (\nSymVar -> (getSV nSymVar, getUserName' nSymVar)) inputs
        userName s = case M.lookup s userNameMap of
                        Just u  | show s /= u -> Just $ "tracks user variable " ++ show u
                        _                     -> Nothing

-- Declare "known" SBV functions here
declSBVFunc :: SMTConfig -> Op -> (String, [String])
declSBVFunc cfg op = (nm, comment ++ body)
  where nm = firstify (firstifyUniqueLen (kdOptions cfg)) op

        comment = ["; Firstified function: " ++ htyp]

        body = case op of
                 SeqOp (SBVReverse KString)                -> mkStringRev
                 SeqOp (SBVReverse (KList k))              -> mkSeqRev  (KList k)
                 SeqOp (SBVZip     k1 k2)                  -> mkZip     k1 k2 Nothing
                 SeqOp (SBVZipWith k1 k2 k3 (SMTLambda f)) -> mkZip     k1 k2 (Just (k3, f))
                 SeqOp (SBVMap     k1 k2    (SMTLambda f)) -> mkMap     k1 k2 f
                 SeqOp (SBVFoldl   k1 k2    (SMTLambda f)) -> mkFoldl   k1 k2 f
                 SeqOp (SBVFoldr   k1 k2    (SMTLambda f)) -> mkFoldr   k1 k2 f
                 SeqOp (SBVFilter  ek       (SMTLambda f)) -> mkFilter  ek    f
                 SeqOp (SBVAll     ek       (SMTLambda f)) -> mkAnyAll  True  ek f
                 SeqOp (SBVAny     ek       (SMTLambda f)) -> mkAnyAll  False ek f
                 SeqOp (SBVConcat  ek)                     -> mkConcat  ek
                 _                                         -> error $ "Data.SBV.declSBVFunc.body: Unexpected internal function: "
                                                                          ++ show (op, nm)

        shf :: String -> [Kind] -> Kind -> String
        shf f args rt = f ++ " :: " ++ intercalate " -> " (map show (args ++ [rt]))

        shh :: String -> ([Kind], Kind) -> ([Kind], Kind) -> String
        shh f (fargs, fret) (args, rt) = f ++ " :: (" ++ intercalate " -> " (map show (fargs ++ [fret])) ++ ") -> "
                                           ++ intercalate " -> " (map show (args ++ [rt]))

        htyp = case op of
                 SeqOp (SBVReverse KString)   -> shf "reverse" [KString] KString
                 SeqOp (SBVReverse k@KList{}) -> shf "reverse" [k] k
                 SeqOp (SBVZip     a b)       -> shf "zip"     [KList a, KList b] (KList (KTuple [a, b]))
                 SeqOp (SBVZipWith a b c _)   -> shh "zipWith" ([a, b], c)  ([KList a, KList b], KList c)
                 SeqOp (SBVMap     a b   _)   -> shh "map"     ([a], b)     ([KList a], KList b)
                 SeqOp (SBVFoldl   a b   _)   -> shh "foldl"   ([b, a], b)  ([b, KList a], b)
                 SeqOp (SBVFoldr   a b   _)   -> shh "foldr"   ([a, b], b)  ([b, KList a], b)
                 SeqOp (SBVFilter  a     _)   -> shh "filter"  ([a], KBool) ([KList a], KList a)
                 SeqOp (SBVAll     a     _)   -> shh "all"     ([a], KBool) ([KList a], KBool)
                 SeqOp (SBVAny     a     _)   -> shh "any"     ([a], KBool) ([KList a], KBool)
                 SeqOp (SBVConcat  a)         -> shf "concat"  [KList (KList a)] (KList a)
                 _                            -> error $ "Data.SBV.declSBVFunc.htyp: Unexpected internal function: " ++ show (op, nm)

        -- in Z3, lambdas are applied with select. In CVC5, it's @. This might change with higher-order features being added to SMTLib in v3
        par x = "(" ++ x ++ ")"
        app f args = par $ unwords $ f : args

        happ f args | isCVC5 = app "@"      (f : args)
                    | True   = app "select" (f : args)

        hd l = app "seq.nth"     [l, "0"]
        tl l = app "seq.extract" [l, "1", app "-" [app "seq.len" [l], "1"]]

        empty   typ     = app "as seq.empty" [typ]
        isEmpty arg typ = app "=" [arg, empty typ]

        isCVC5 = case name (solver cfg) of
                   CVC5 -> True
                   _    -> False

        mkStringRev = [ "(define-fun-rec " ++ nm ++ " ((str String)) String"
                      , "                (ite (= str \"\")"
                      , "                     \"\""
                      , "                     (str.++ (" ++ nm ++ " (str.substr str 1 (- (str.len str) 1)))"
                      , "                             (str.substr str 0 1))))"
                      ]


        mkSeqRev k = [ "(define-fun-rec " ++ nm ++ " ((lst " ++ t ++ ")) " ++ t
                     , "                (ite " ++ isEmpty "lst" t
                     , "                     " ++ empty t
                     , "                     (seq.++ " ++ app nm [tl "lst"] ++ " (seq.unit " ++ hd "lst" ++ "))))"
                     ]
          where t = smtType k

        -- [a] -> [b] -> [(a, b)]
        -- [a] -> [b] -> (a -> b -> c) -> [c]
        mkZip a b mbcF = [ "(define-fun-rec " ++ nm ++ " ((lst1 " ++ tla ++ ") (lst2 " ++ tlb ++ ")) " ++ tlr
                         , "               (ite " ++ app "or" [isEmpty "lst1" tla, isEmpty "lst2" tlb]
                         , "                    " ++ empty tlr
                         , "                    (seq.++ (seq.unit " ++ mkTup (hd "lst1") (hd "lst2") ++ ") " ++ app nm [tl "lst1", tl "lst2"] ++ ")))"
                         ]
         where tla = smtType (KList a)
               tlb = smtType (KList b)
               tlr = case mbcF of
                       Nothing     -> smtType (KList (KTuple [a, b]))
                       Just (c, _) -> smtType (KList c)

               mkTup x y = case mbcF of
                             Just (_, f) -> happ f   [x, y]
                             Nothing     -> app  tup [x, y]
               tup = app "as" ["mkSBVTuple2", app "SBVTuple2" [smtType a, smtType b]]

        -- (b -> a -> b) -> b -> [a] -> b
        mkFoldl a b f = [ "(define-fun-rec " ++ nm ++ " ((base " ++ tb ++ ") (lst " ++ tla ++ ")) " ++ tb
                        , "                (ite " ++ isEmpty "lst" tla
                        , "                     base"
                        , "                     " ++ app nm [happ f ["base", hd "lst"], tl "lst"] ++ "))"
                        ]
           where tla = smtType (KList a)
                 tb  = smtType b

        -- (a -> b -> b) -> b -> [a] -> b
        mkFoldr a b f = [ "(define-fun-rec " ++ nm ++ " ((base " ++ tb ++ ") (lst " ++ tla ++ ")) " ++ tb
                        , "                (ite " ++ isEmpty "lst" tla
                        , "                     base"
                        , "                     " ++ happ f [hd "lst", app nm ["base", tl "lst"]] ++ "))"
                        ]
           where tla = smtType (KList a)
                 tb  = smtType b

        -- (a -> b) -> [a] -> [b]
        mkMap a b f = [ "(define-fun-rec " ++ nm ++ " ((lst " ++ tla ++ ")) " ++ tlb
                      , "              (ite " ++ isEmpty "lst" tla
                      , "                   " ++ empty tlb
                      , "                   (seq.++ (seq.unit " ++ happ f [hd "lst"] ++ ")"
                      , "                           " ++ app nm [tl "lst"] ++ ")))"
                      ]
           where tla = smtType (KList a)
                 tlb = smtType (KList b)

        -- (a -> Bool) -> [a] -> [a]
        mkFilter a f = [ "(define-fun-rec " ++ nm ++ " ((lst " ++ tla ++ ")) " ++ tla
                       , "                (ite " ++ isEmpty "lst" tla
                       , "                     " ++ empty tla
                       , "                     (let ((rest (" ++ nm ++ " " ++ tl "lst" ++ ")))"
                       , "                          (ite " ++ happ f [hd "lst"]
                       , "                               (seq.++ (seq.unit " ++ hd "lst" ++ ") rest)"
                       , "                                       rest))))"
                       ]
          where tla = smtType (KList a)

        -- (a -> Bool) -> [a] -> Bool
        mkAnyAll isAll a f = [ "(define-fun-rec " ++ nm ++ " ((lst " ++ tla ++ ")) Bool"
                             , "                (ite " ++ isEmpty "lst" tla
                             , "                     " ++ base
                             , "                     " ++ app conn [happ f [hd "lst"], app nm [tl "lst"]] ++ "))"
                             ]
          where tla = smtType (KList a)
                (base, conn) | isAll = ("true",  "and")
                             | True  = ("false", "or")

        -- [[a]] -> [a]
        mkConcat a = [ "(define-fun-rec " ++ nm ++ " ((lst " ++ tlla ++ ")) " ++ tla
                     , "                (ite " ++ isEmpty "lst" tlla
                     , "                     " ++ empty tla
                     , "                     (seq.++ " ++ hd "lst" ++ " (" ++ nm ++ " " ++ tl "lst" ++ "))))"
                     ]
         where tla  = smtType (KList a)
               tlla = smtType (KList (KList a))

-- | Declare new sorts
declSort :: (String, Maybe [String]) -> [String]
declSort (s, _)
  | s == "RoundingMode" -- built-in-sort; so don't declare.
  = []
declSort (s, Nothing) = [ "(declare-sort " ++ s ++ " 0)  ; N.B. Uninterpreted sort." 
                        , "(declare-fun " ++ witnessName s ++ " () " ++ s ++ ")"
                        ]
declSort (s, Just fs) = [ "(declare-datatypes ((" ++ s ++ " 0)) ((" ++ unwords (map (\c -> "(" ++ c ++ ")") fs) ++ ")))"
                        , "(define-fun " ++ s ++ "_constrIndex ((x " ++ s ++ ")) Int"
                        ] ++ ["   " ++ body fs (0::Int)] ++ [")"]
        where body []     _ = ""
              body [_]    i = show i
              body (c:cs) i = "(ite (= x " ++ c ++ ") " ++ show i ++ " " ++ body cs (i+1) ++ ")"

-- | Declare tuple datatypes
--
-- eg:
--
-- @
-- (declare-datatypes ((SBVTuple2 2)) ((par (T1 T2)
--                                     ((mkSBVTuple2 (proj_1_SBVTuple2 T1)
--                                                   (proj_2_SBVTuple2 T2))))))
-- @
declTuple :: Int -> [String]
declTuple arity
  | arity == 0 = ["(declare-datatypes ((SBVTuple0 0)) (((mkSBVTuple0))))"]
  | arity == 1 = error "Data.SBV.declTuple: Unexpected one-tuple"
  | True       =    (l1 ++ "(par (" ++ unwords [param i | i <- [1..arity]] ++ ")")
                 :  [pre i ++ proj i ++ post i    | i <- [1..arity]]
  where l1     = "(declare-datatypes ((SBVTuple" ++ show arity ++ " " ++ show arity ++ ")) ("
        l2     = replicate (length l1) ' ' ++ "((mkSBVTuple" ++ show arity ++ " "
        tab    = replicate (length l2) ' '

        pre 1  = l2
        pre _  = tab

        proj i = "(proj_" ++ show i ++ "_SBVTuple" ++ show arity ++ " " ++ param i ++ ")"

        post i = if i == arity then ")))))" else ""

        param i = "T" ++ show i

-- | Find the set of tuple sizes to declare, eg (2-tuple, 5-tuple).
-- NB. We do *not* need to recursively go into list/tuple kinds here,
-- because register-kind function automatically registers all subcomponent
-- kinds, thus everything we need is available at the top-level.
findTupleArities :: Set Kind -> [Int]
findTupleArities ks = Set.toAscList
                    $ Set.map length
                    $ Set.fromList [ tupKs | KTuple tupKs <- Set.toList ks ]

-- | Is @Either@ being used?
containsSum :: Set Kind -> Bool
containsSum = not . Set.null . Set.filter isEither

-- | Is @Maybe@ being used?
containsMaybe :: Set Kind -> Bool
containsMaybe = not . Set.null . Set.filter isMaybe

-- | Is @Rational@ being used?
containsRationals :: Set Kind -> Bool
containsRationals = not . Set.null . Set.filter isRational

declSum :: [String]
declSum = [ "(declare-datatypes ((SBVEither 2)) ((par (T1 T2)"
          , "                                    ((left_SBVEither  (get_left_SBVEither  T1))"
          , "                                     (right_SBVEither (get_right_SBVEither T2))))))"
          ]

declMaybe :: [String]
declMaybe = [ "(declare-datatypes ((SBVMaybe 1)) ((par (T)"
            , "                                    ((nothing_SBVMaybe)"
            , "                                     (just_SBVMaybe (get_just_SBVMaybe T))))))"
            ]

-- Internally, we do *not* keep the rationals in reduced form! So, the boolean operators explicitly do the math
-- to make sure equivalent values are treated correctly.
declRationals :: [String]
declRationals = [ "(declare-datatype SBVRational ((SBV.Rational (sbv.rat.numerator Int) (sbv.rat.denominator Int))))"
                , ""
                , "(define-fun sbv.rat.eq ((x SBVRational) (y SBVRational)) Bool"
                , "   (= (* (sbv.rat.numerator   x) (sbv.rat.denominator y))"
                , "      (* (sbv.rat.denominator x) (sbv.rat.numerator   y)))"
                , ")"
                , ""
                , "(define-fun sbv.rat.notEq ((x SBVRational) (y SBVRational)) Bool"
                , "   (not (sbv.rat.eq x y))"
                , ")"
                , ""
                , "(define-fun sbv.rat.lt ((x SBVRational) (y SBVRational)) Bool"
                , "   (<  (* (sbv.rat.numerator   x) (sbv.rat.denominator y))"
                , "       (* (sbv.rat.denominator x) (sbv.rat.numerator   y)))"
                , ")"
                , ""
                , "(define-fun sbv.rat.leq ((x SBVRational) (y SBVRational)) Bool"
                , "   (<= (* (sbv.rat.numerator   x) (sbv.rat.denominator y))"
                , "       (* (sbv.rat.denominator x) (sbv.rat.numerator   y)))"
                , ")"
                , ""
                , "(define-fun sbv.rat.plus ((x SBVRational) (y SBVRational)) SBVRational"
                , "   (SBV.Rational (+ (* (sbv.rat.numerator   x) (sbv.rat.denominator y))"
                , "                    (* (sbv.rat.denominator x) (sbv.rat.numerator   y)))"
                , "                 (* (sbv.rat.denominator x) (sbv.rat.denominator y)))"
                , ")"
                , ""
                , "(define-fun sbv.rat.minus ((x SBVRational) (y SBVRational)) SBVRational"
                , "   (SBV.Rational (- (* (sbv.rat.numerator   x) (sbv.rat.denominator y))"
                , "                    (* (sbv.rat.denominator x) (sbv.rat.numerator   y)))"
                , "                 (* (sbv.rat.denominator x) (sbv.rat.denominator y)))"
                , ")"
                , ""
                , "(define-fun sbv.rat.times ((x SBVRational) (y SBVRational)) SBVRational"
                , "   (SBV.Rational (* (sbv.rat.numerator   x) (sbv.rat.numerator y))"
                , "                 (* (sbv.rat.denominator x) (sbv.rat.denominator y)))"
                , ")"
                , ""
                , "(define-fun sbv.rat.uneg ((x SBVRational)) SBVRational"
                , "   (SBV.Rational (* (- 1) (sbv.rat.numerator x)) (sbv.rat.denominator x))"
                , ")"
                , ""
                , "(define-fun sbv.rat.abs ((x SBVRational)) SBVRational"
                , "   (SBV.Rational (abs (sbv.rat.numerator x)) (sbv.rat.denominator x))"
                , ")"
                ]

-- | Convert in a query context.
-- NB. We do not store everything in @newKs@ below, but only what we need
-- to do as an extra in the incremental context. See `Data.SBV.Core.Symbolic.registerKind`
-- for a list of what we include, in case something doesn't show up
-- and you need it!
cvtInc :: SMTLibIncConverter [String]
cvtInc curProgInfo inps newKs (_, consts) tbls uis (SBVPgm asgnsSeq) cstrs cfg =
            -- any new settings?
               settings
            -- sorts
            ++ concatMap declSort [(s, dt) | KUserSort s dt <- newKinds]
            -- tuples. NB. Only declare the new sizes, old sizes persist.
            ++ concatMap declTuple (findTupleArities newKs)
            -- sums
            ++ (if containsSum   newKs then declSum   else [])
            ++ (if containsMaybe newKs then declMaybe else [])
            -- constants
            ++ concatMap (declConst cfg) consts
            -- inputs
            ++ concatMap declInp inps
            -- uninterpreteds
            ++ concatMap (declUI curProgInfo) uis
            -- table declarations
            ++ tableDecls
            -- expressions
            ++ concatMap (declDef curProgInfo cfg tableMap) (F.toList asgnsSeq)
            -- table setups
            ++ concat tableAssigns
            -- extra constraints
            ++ map (\(isSoft, attr, v) -> "(assert" ++ (if isSoft then "-soft " else " ") ++ addAnnotations attr (cvtSV v) ++ ")") (F.toList cstrs)
  where rm = roundingMode cfg

        newKinds = Set.toList newKs

        declInp (getSV -> s) = declareFun s (SBVType [kindOf s]) Nothing

        (tableMap, allTables) = (tm, ct ++ nct)
            where (tm, ct, nct) = constructTables rm consts tbls

        (tableDecls, tableAssigns) = unzip $ map mkTable allTables

        -- If we need flattening in models, do emit the required lines if preset
        settings
          | any needsFlattening newKinds
          = concat (catMaybes [supportsFlattenedModels solverCaps])
          | True
          = []
          where solverCaps = capabilities (solver cfg)

declDef :: ProgInfo -> SMTConfig -> TableMap -> (SV, SBVExpr) -> [String]
declDef curProgInfo cfg tableMap (s, expr) =
        case expr of
          SBVApp  (Label m) [e] -> defineFun cfg (s, cvtSV                                   e) (Just m)
          e                     -> defineFun cfg (s, cvtExp cfg curProgInfo caps rm tableMap e) Nothing
  where caps = capabilities (solver cfg)
        rm   = roundingMode cfg

defineFun :: SMTConfig -> (SV, String) -> Maybe String -> [String]
defineFun cfg (s, def) mbComment
   | hasDefFun = ["(define-fun "  ++ varT ++ " " ++ def ++ ")" ++ cmnt]
   | True      = [ "(declare-fun " ++ varT ++ ")" ++ cmnt
                 , "(assert (= " ++ var ++ " " ++ def ++ "))"
                 ]
  where var  = show s
        varT = var ++ " " ++ svFunType [] s
        cmnt = maybe "" (" ; " ++) mbComment

        hasDefFun = supportsDefineFun $ capabilities (solver cfg)

-- Declare constants. NB. We don't declare true/false; but just inline those as necessary
declConst :: SMTConfig -> (SV, CV) -> [String]
declConst cfg (s, c)
  | s == falseSV || s == trueSV
  = []
  | True
  = defineFun cfg (s, cvtCV (roundingMode cfg) c) Nothing

-- Make a function equality of nm against the internal function fun
mkRelEq :: String -> (String, String) -> Kind -> String
mkRelEq nm (fun, order) ak = res
   where lhs = "(" ++ nm ++ " x y)" 
         rhs = "((_ " ++ fun ++ " " ++ order ++ ") x y)"
         tk  = smtType ak
         res = "(forall ((x " ++ tk ++ ") (y " ++ tk ++ ")) (= " ++ lhs ++ " " ++ rhs ++ "))"

declUI :: ProgInfo -> (String, (Bool, Maybe [String], SBVType)) -> [String]
declUI ProgInfo{progTransClosures} (i, (_, _, t)) = declareName i t Nothing ++ declClosure
  where declClosure | Just external <- lookup i progTransClosures
                    =  declareName external t Nothing
                    ++ ["(assert " ++ mkRelEq external ("transitive-closure", i) (argKind t) ++ ")"]
                    | True
                    = []

        argKind (SBVType [ka, _, KBool]) = ka
        argKind _                        = error $ "declUI: Unexpected type for name: " ++ show (i, t)

-- Note that even though we get all user defined-functions here (i.e., lambda and axiom), we can only have defined-functions
-- and axioms. We spit axioms as is; and topologically sort the definitions.
declUserFuns :: [(SMTDef, SBVType)] -> [String]
declUserFuns ds
  | not (null lambdas)
  = error $ unlines $ "Data.SBV.declUserFuns: Unexpected anonymous functions in declDef:" : map show lambdas
  | True
  = declFuncs others
  where (lambdas, others) = partition (isLam . fst) ds
        isLam SMTLam{} = True
        isLam SMTDef{} = False

-- We need to topologically sort the user given definitions and axioms and put them in the proper order and construct.
-- Note that there are no anonymous functions at this level.
declFuncs :: [(SMTDef, SBVType)] -> [String]
declFuncs ds = map declGroup sorted
  where mkNode d = (d, getKey d, getDeps d)

        getKey (d, _) = case d of
                         SMTDef n _ _ _ _ _ -> n
                         SMTLam{}           -> error $ "Data.SBV.declFuns: Unexpected definition kind: " ++ show d

        getDeps (SMTDef _ _ d _ _ _, _) = d
        getDeps (l@SMTLam{}, t)         = error $ "Data.SBV.declFuns: Unexpected definition: " ++ show (l, t)

        mkDecl Nothing  rt = "() "    ++ rt
        mkDecl (Just p) rt = p ++ " " ++ rt

        sorted = DG.stronglyConnComp (map mkNode ds)

        declGroup (DG.AcyclicSCC b)  = declUserDef False b
        declGroup (DG.CyclicSCC  bs) = case bs of
                                         []  -> error "Data.SBV.declFuns: Impossible happened: an empty cyclic group was returned!"
                                         [x] -> declUserDef True x
                                         xs  -> declUserDefMulti xs

        declUserDef _ d@(SMTLam{}, _) = error $ "Data.SBV.declFuns: Unexpected anonymous lambda in user-defined functions: " ++ show d
        declUserDef isRec (SMTDef nm fk deps _ops param body, ty) = ("; " ++ nm ++ " :: " ++ show ty ++ recursive ++ frees ++ "\n") ++ s
           where (recursive, definer) | isRec = (" [Recursive]", "define-fun-rec")
                                      | True  = ("",             "define-fun")

                 otherDeps = filter (/= nm) deps
                 frees | null otherDeps = ""
                       | True           = " [Refers to: " ++ intercalate ", " otherDeps ++ "]"

                 decl = mkDecl param (smtType fk)

                 s = "(" ++ definer ++ " " ++ nm ++ " " ++ decl ++ "\n" ++ body 2 ++ ")"

        -- declare a bunch of mutually-recursive functions
        declUserDefMulti bs = render $ map collect bs
          where collect d@(SMTLam{}, _) = error $ "Data.SBV.declFuns: Unexpected lambda in user-defined mutual-recursion group: " ++ show d
                collect (SMTDef nm fk deps _ops param body, ty) = (deps, nm, ty, '(' : nm ++ " " ++  decl ++ ")", body 3)
                  where decl = mkDecl param (smtType fk)

                render defs = intercalate "\n" $
                                  [ "; " ++ intercalate ", " [n ++ " :: " ++ show ty | (_, n, ty, _, _) <- defs]
                                  , "(define-funs-rec"
                                  ]
                               ++ [ open i ++ param d ++ close1 i | (i, d) <- zip [1..] defs]
                               ++ [ open i ++ dump  d ++ close2 i | (i, d) <- zip [1..] defs]
                     where open 1 = "  ("
                           open _ = "   "

                           param (_deps, _nm, _ty, p, _body) = p

                           dump (deps, nm, ty, _, body) = "; Definition of: " ++ nm ++ " :: " ++ show ty ++ ". [Refers to: " ++ intercalate ", " deps ++ "]"
                                                        ++ "\n" ++ body

                           ld = length defs

                           close1 n = if n == ld then ")"  else ""
                           close2 n = if n == ld then "))" else ""

mkTable :: (((Int, Kind, Kind), [SV]), [String]) -> (String, [String])
mkTable (((i, ak, rk), _elts), is) = (decl, zipWith wrap [(0::Int)..] is ++ setup)
  where t       = "table" ++ show i
        decl    = "(declare-fun " ++ t ++ " (" ++ smtType ak ++ ") " ++ smtType rk ++ ")"

        -- Arrange for initializers
        mkInit idx   = "table" ++ show i ++ "_initializer_" ++ show (idx :: Int)
        initializer  = "table" ++ show i ++ "_initializer"

        wrap index s = "(define-fun " ++ mkInit index ++ " () Bool " ++ s ++ ")"

        lis  = length is

        setup
          | lis == 0       = [ "(define-fun " ++ initializer ++ " () Bool true) ; no initialization needed"
                             ]
          | lis == 1       = [ "(define-fun " ++ initializer ++ " () Bool " ++ mkInit 0 ++ ")"
                             , "(assert " ++ initializer ++ ")"
                             ]
          | True           = [ "(define-fun " ++ initializer ++ " () Bool (and " ++ unwords (map mkInit [0..lis - 1]) ++ "))"
                             , "(assert " ++ initializer ++ ")"
                             ]
nonConstTable :: (((Int, Kind, Kind), [SV]), [String]) -> String
nonConstTable (((i, ak, rk), _elts), _) = decl
  where t    = "table" ++ show i
        decl = "(declare-fun " ++ t ++ " (" ++ smtType ak ++ ") " ++ smtType rk ++ ")"

constructTables :: RoundingMode -> [(SV, CV)] -> [((Int, Kind, Kind), [SV])]
                -> ( IM.IntMap String                            -- table enumeration
                   , [(((Int, Kind, Kind), [SV]), [String])]     -- constant tables
                   , [(((Int, Kind, Kind), [SV]), [String])]     -- non-constant tables
                   )
constructTables rm consts tbls = (tableMap, constTables, nonConstTables)
 where allTables      = [(t, genTableData rm (map fst consts) t) | t <- tbls]
       constTables    = [(t, d) | (t, Left  d) <- allTables]
       nonConstTables = [(t, d) | (t, Right d) <- allTables]
       tableMap       = IM.fromList $ map grab allTables

       grab (((t, _, _), _), _) = (t, "table" ++ show t)

-- Left if all constants, Right if otherwise
genTableData :: RoundingMode -> [SV] -> ((Int, Kind, Kind), [SV]) -> Either [String] [String]
genTableData rm consts ((i, aknd, _), elts)
  | null post = Left  (map (mkEntry . snd) pre)
  | True      = Right (map (mkEntry . snd) (pre ++ post))
  where (pre, post) = partition fst (zipWith mkElt elts [(0::Int)..])
        t           = "table" ++ show i

        mkElt x k   = (isReady, (idx, cvtSV x))
          where idx = cvtCV rm (mkConstCV aknd k)
                isReady = x `Set.member` constsSet

        mkEntry (idx, v) = "(= (" ++ t ++ " " ++ idx ++ ") " ++ v ++ ")"

        constsSet = Set.fromList consts

svType :: SV -> String
svType s = smtType (kindOf s)

svFunType :: [SV] -> SV -> String
svFunType ss s = "(" ++ unwords (map svType ss) ++ ") " ++ svType s

cvtType :: SBVType -> String
cvtType (SBVType []) = error "SBV.SMT.SMTLib2.cvtType: internal: received an empty type!"
cvtType (SBVType xs) = "(" ++ unwords (map smtType body) ++ ") " ++ smtType ret
  where (body, ret) = (init xs, last xs)

type TableMap = IM.IntMap String

-- Present an SV, simply show
cvtSV :: SV -> String
cvtSV = show

cvtCV :: RoundingMode -> CV -> String
cvtCV = cvToSMTLib

getTable :: TableMap -> Int -> String
getTable m i
  | Just tn <- i `IM.lookup` m = tn
  | True                       = "table" ++ show i  -- constant tables are always named this way

cvtExp :: SMTConfig -> ProgInfo -> SolverCapabilities -> RoundingMode -> TableMap -> SBVExpr -> String
cvtExp cfg curProgInfo caps rm tableMap expr@(SBVApp _ arguments) = sh expr
  where hasPB       = supportsPseudoBooleans caps
        hasInt2bv   = supportsInt2bv         caps
        hasDistinct = supportsDistinct       caps
        specialRels = progSpecialRels        curProgInfo

        bvOp     = all isBounded   arguments
        intOp    = any isUnbounded arguments
        ratOp    = any isRational  arguments
        realOp   = any isReal      arguments
        fpOp     = any (\a -> isDouble a || isFloat a || isFP a) arguments
        boolOp   = all isBoolean   arguments
        charOp   = any isChar      arguments
        stringOp = any isString    arguments
        listOp   = any isList      arguments

        bad | intOp = error $ "SBV.SMTLib2: Unsupported operation on unbounded integers: " ++ show expr
            | True  = error $ "SBV.SMTLib2: Unsupported operation on real values: " ++ show expr

        ensureBVOrBool = bvOp || boolOp || bad
        ensureBV       = bvOp || bad

        addRM s = s ++ " " ++ smtRoundingMode rm

        hd _ (a:_) = a
        hd w []    = error $ "Impossible: " ++ w ++ ": Received empty list of args!"

        -- lift a binary op
        lift2  o _ [x, y] = "(" ++ o ++ " " ++ x ++ " " ++ y ++ ")"
        lift2  o _ sbvs   = error $ "SBV.SMTLib2.sh.lift2: Unexpected arguments: "   ++ show (o, sbvs)

        -- lift an arbitrary arity operator
        liftN o _ xs = "(" ++ o ++ " " ++ unwords xs ++ ")"

        -- lift a binary operation with rounding-mode added; used for floating-point arithmetic
        lift2WM o fo | fpOp = lift2 (addRM fo)
                     | True = lift2 o

        lift1FP o fo | fpOp = lift1 fo
                     | True = lift1 o

        liftAbs sgned args | fpOp        = lift1 "fp.abs" sgned args
                           | intOp       = lift1 "abs"    sgned args
                           | bvOp, sgned = mkAbs fArg "bvslt" "bvneg"
                           | bvOp        = fArg
                           | True        = mkAbs fArg "<"     "-"
          where fArg = hd "liftAbs" args
                mkAbs x cmp neg = "(ite " ++ ltz ++ " " ++ nx ++ " " ++ x ++ ")"
                  where ltz = "(" ++ cmp ++ " " ++ x ++ " " ++ z ++ ")"
                        nx  = "(" ++ neg ++ " " ++ x ++ ")"
                        z   = cvtCV rm (mkConstCV (kindOf (hd "liftAbs.arguments" arguments)) (0::Integer))

        lift2B bOp vOp
          | boolOp = lift2 bOp
          | True   = lift2 vOp

        lift1B bOp vOp
          | boolOp = lift1 bOp
          | True   = lift1 vOp

        eqBV  = lift2 "="
        neqBV = liftN "distinct"

        equal sgn sbvs
          | fpOp = lift2 "fp.eq" sgn sbvs
          | True = lift2 "="     sgn sbvs

        -- Do not use distinct on floats; because +0/-0, and NaNs mess
        -- up the meaning. Just go with reqular equals.
        notEqual sgn sbvs
          | fpOp || not hasDistinct = liftP sbvs
          | True                    = liftN "distinct" sgn sbvs
          where liftP xs@[_, _] = "(not " ++ equal sgn xs ++ ")"
                liftP args      = "(and " ++ unwords (walk args) ++ ")"

                walk []     = []
                walk (e:es) = map (\e' -> liftP [e, e']) es ++ walk es

        lift2S oU oS sgn = lift2 (if sgn then oS else oU) sgn
        liftNS oU oS sgn = liftN (if sgn then oS else oU) sgn

        lift2Cmp o fo | fpOp = lift2 fo
                      | True = lift2 o

        unintComp o [a, b]
          | KUserSort s (Just _) <- kindOf (hd "unintComp" arguments)
          = let idx v = "(" ++ s ++ "_constrIndex " ++ v ++ ")" in "(" ++ o ++ " " ++ idx a ++ " " ++ idx b ++ ")"
        unintComp o sbvs = error $ "SBV.SMT.SMTLib2.sh.unintComp: Unexpected arguments: "   ++ show (o, sbvs, map kindOf arguments)

        stringOrChar KString = True
        stringOrChar KChar   = True
        stringOrChar _       = False
        stringCmp swap o [a, b]
          | stringOrChar (kindOf (hd "stringCmp" arguments))
          = let (a1, a2) | swap = (b, a)
                         | True = (a, b)
            in "(" ++ o ++ " " ++ a1 ++ " " ++ a2 ++ ")"
        stringCmp _ o sbvs = error $ "SBV.SMT.SMTLib2.sh.stringCmp: Unexpected arguments: " ++ show (o, sbvs)

        -- NB. Likewise for sequences
        seqCmp swap o [a, b]
          | KList{} <- kindOf (hd "seqCmp" arguments)
          = let (a1, a2) | swap = (b, a)
                         | True = (a, b)
            in "(" ++ o ++ " " ++ a1 ++ " " ++ a2 ++ ")"
        seqCmp _ o sbvs = error $ "SBV.SMT.SMTLib2.sh.seqCmp: Unexpected arguments: " ++ show (o, sbvs)

        lift1  o _ [x]    = "(" ++ o ++ " " ++ x ++ ")"
        lift1  o _ sbvs   = error $ "SBV.SMT.SMTLib2.sh.lift1: Unexpected arguments: "   ++ show (o, sbvs)

        -- We fully qualify the constructor with their types to work around type checking issues
        -- Note that this is rather bizarre, as we're tagging the constructor with its *result* type,
        -- not its full function type as one would expect. But this is per the spec: Pg. 27 of SMTLib 2.6 spec
        -- says:
        --
        --    To simplify sort checking, a function symbol in a term can be annotated with one of its result sorts sigma.
        --
        -- I wish it was the full type here not just the result, but we go with the spec. Also see: <http://github.com/Z3Prover/z3/issues/2135>
        -- and in particular <http://github.com/Z3Prover/z3/issues/2135#issuecomment-477636435>
        dtConstructor fld args res = "((as " ++ fld ++ " " ++ smtType res ++ ") " ++ unwords (map cvtSV args) ++ ")"

        -- Similarly, we fully qualify the accessors with their types to work around type checking issues
        -- Unfortunately, z3 and CVC4 are behaving differently, so we tie this ascription to a solver capability.
        dtAccessor fld params res
           | supportsDirectAccessors caps = dResult
           | True                         = aResult
          where dResult = "(_ is " ++ fld ++ ")"
                ps      = " (" ++ unwords (map smtType params) ++ ") "
                aResult = "(_ is (" ++ fld ++ ps ++ smtType res ++ "))"

        firstifiedName = firstify (firstifyUniqueLen (kdOptions cfg))

        sh (SBVApp Ite [a, b, c]) = "(ite " ++ cvtSV a ++ " " ++ cvtSV b ++ " " ++ cvtSV c ++ ")"

        sh (SBVApp (LkUp (t, aKnd, _, l) i e) [])
          | needsCheck = "(ite " ++ cond ++ cvtSV e ++ " " ++ lkUp ++ ")"
          | True       = lkUp
          where needsCheck = case aKnd of
                              KBool         -> (2::Integer) > fromIntegral l
                              KBounded _ n  -> (2::Integer)^n > fromIntegral l
                              KUnbounded    -> True
                              KUserSort s _ -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected uninterpreted valued index: " ++ s
                              KReal         -> error "SBV.SMT.SMTLib2.cvtExp: unexpected real valued index"
                              KFloat        -> error "SBV.SMT.SMTLib2.cvtExp: unexpected float valued index"
                              KDouble       -> error "SBV.SMT.SMTLib2.cvtExp: unexpected double valued index"
                              KFP{}         -> error "SBV.SMT.SMTLib2.cvtExp: unexpected arbitrary float valued index"
                              KRational{}   -> error "SBV.SMT.SMTLib2.cvtExp: unexpected rational valued index"
                              KChar         -> error "SBV.SMT.SMTLib2.cvtExp: unexpected char valued index"
                              KString       -> error "SBV.SMT.SMTLib2.cvtExp: unexpected string valued index"
                              KList k       -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected list valued: " ++ show k
                              KSet  k       -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected set valued: " ++ show k
                              KTuple k      -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected tuple valued: " ++ show k
                              KMaybe k      -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected maybe valued: " ++ show k
                              KEither k1 k2 -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected sum valued: " ++ show (k1, k2)
                              KArray  k1 k2 -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected array valued: " ++ show (k1, k2)

                lkUp = "(" ++ getTable tableMap t ++ " " ++ cvtSV i ++ ")"

                cond
                 | hasSign i = "(or " ++ le0 ++ " " ++ gtl ++ ") "
                 | True      = gtl ++ " "

                (less, leq) = case aKnd of
                                KBool         -> error "SBV.SMT.SMTLib2.cvtExp: unexpected boolean valued index"
                                KBounded{}    -> if hasSign i then ("bvslt", "bvsle") else ("bvult", "bvule")
                                KUnbounded    -> ("<", "<=")
                                KReal         -> ("<", "<=")
                                KFloat        -> ("fp.lt", "fp.leq")
                                KDouble       -> ("fp.lt", "fp.leq")
                                KRational     -> ("sbv.rat.lt", "sbv.rat.leq")
                                KFP{}         -> ("fp.lt", "fp.leq")
                                KChar         -> error "SBV.SMT.SMTLib2.cvtExp: unexpected string valued index"
                                KString       -> error "SBV.SMT.SMTLib2.cvtExp: unexpected string valued index"
                                KUserSort s _ -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected uninterpreted valued index: " ++ s
                                KList k       -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected sequence valued index: " ++ show k
                                KSet  k       -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected set valued index: " ++ show k
                                KTuple k      -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected tuple valued index: " ++ show k
                                KMaybe k      -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected maybe valued index: " ++ show k
                                KEither k1 k2 -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected sum valued index: " ++ show (k1, k2)
                                KArray  k1 k2 -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected array valued index: " ++ show (k1, k2)

                mkCnst = cvtCV rm . mkConstCV (kindOf i)
                le0  = "(" ++ less ++ " " ++ cvtSV i ++ " " ++ mkCnst 0 ++ ")"
                gtl  = "(" ++ leq  ++ " " ++ mkCnst l ++ " " ++ cvtSV i ++ ")"

        sh (SBVApp (KindCast f t) [a]) = handleKindCast hasInt2bv f t (cvtSV a)

        sh (SBVApp (ArrayLambda s) [])        = show s
        sh (SBVApp ReadArray       [a, i])    = "(select " ++ cvtSV a ++ " " ++ cvtSV i ++ ")"
        sh (SBVApp WriteArray      [a, i, e]) = "(store "  ++ cvtSV a ++ " " ++ cvtSV i ++ " " ++ cvtSV e ++ ")"

        sh (SBVApp (Uninterpreted nm) [])   = nm
        sh (SBVApp (Uninterpreted nm) args) = "(" ++ nm ++ " " ++ unwords (map cvtSV args) ++ ")"

        sh (SBVApp (QuantifiedBool _ i) [])   = i
        sh (SBVApp (QuantifiedBool _ i) args) = error $ "SBV.SMT.SMTLib2.cvtExp: unexpected arguments to quantified boolean: " ++ show (i, args)

        sh a@(SBVApp (SpecialRelOp k o) args)
          | not (null args)
          = error $ "SBV.SMT.SMTLib2.cvtExp: unexpected arguments to special op: " ++ show a
          | True
          = let order = case o `elemIndex` specialRels of
                          Just i -> i
                          Nothing -> error $ unlines [ "SBV.SMT.SMTLib2.cvtExp: Cannot find " ++ show o ++ " in the special-relations list."
                                                     , "Known relations: " ++ intercalate ", " (map show specialRels)
                                                     ]
                asrt nm fun = mkRelEq nm (fun, show order) k
            in case o of
                 IsPartialOrder         nm -> asrt nm "partial-order"
                 IsLinearOrder          nm -> asrt nm "linear-order"
                 IsTreeOrder            nm -> asrt nm "tree-order"
                 IsPiecewiseLinearOrder nm -> asrt nm "piecewise-linear-order"

        sh (SBVApp (Divides n) [a]) = "((_ divisible " ++ show n ++ ") " ++ cvtSV a ++ ")"

        sh (SBVApp (Extract i j) [a]) | ensureBV = "((_ extract " ++ show i ++ " " ++ show j ++ ") " ++ cvtSV a ++ ")"

        sh (SBVApp (Rol i) [a])
           | bvOp  = rot "rotate_left"  i a
           | True  = bad

        sh (SBVApp (Ror i) [a])
           | bvOp  = rot  "rotate_right" i a
           | True  = bad

        sh (SBVApp Shl [a, i])
           | bvOp   = shft "bvshl"  "bvshl" a i
           | True   = bad

        sh (SBVApp Shr [a, i])
           | bvOp  = shft "bvlshr" "bvashr" a i
           | True  = bad

        sh (SBVApp (ZeroExtend i) [a])
          | bvOp = "((_ zero_extend " ++ show i ++ ") " ++ cvtSV a ++ ")"
          | True = bad

        sh (SBVApp (SignExtend i) [a])
          | bvOp = "((_ sign_extend " ++ show i ++ ") " ++ cvtSV a ++ ")"
          | True = bad

        sh (SBVApp op args)
          | Just f <- lookup op smtBVOpTable, ensureBVOrBool
          = f (any hasSign args) (map cvtSV args)
          where -- The first 4 operators below do make sense for Integer's in Haskell, but there's
                -- no obvious counterpart for them in the SMTLib translation.
                -- TODO: provide support for these.
                smtBVOpTable = [ (And,  lift2B "and" "bvand")
                               , (Or,   lift2B "or"  "bvor")
                               , (XOr,  lift2B "xor" "bvxor")
                               , (Not,  lift1B "not" "bvnot")
                               , (Join, lift2 "concat")
                               ]

        sh (SBVApp (Label _) [a]) = cvtSV a  -- This won't be reached; but just in case!

        sh (SBVApp (IEEEFP (FP_Cast kFrom kTo m)) args) = handleFPCast kFrom kTo (cvtSV m) (unwords (map cvtSV args))
        sh (SBVApp (IEEEFP w                    ) args) = "(" ++ show w ++ " " ++ unwords (map cvtSV args) ++ ")"

        sh (SBVApp (NonLinear w) args) = "(" ++ show w ++ " " ++ unwords (map cvtSV args) ++ ")"

        sh (SBVApp (PseudoBoolean pb) args)
          | hasPB = handlePB pb args'
          | True  = reducePB pb args'
          where args' = map cvtSV args

        sh (SBVApp (OverflowOp op) args) = "(" ++ show op ++ " " ++ unwords (map cvtSV args) ++ ")"

        -- Note the unfortunate reversal in StrInRe..
        sh (SBVApp (StrOp (StrInRe r)) args) = "(str.in.re " ++ unwords (map cvtSV args) ++ " " ++ regExpToSMTString r ++ ")"
        -- StrUnit is no-op, since a character in SMTLib is the same as a string
        sh (SBVApp (StrOp StrUnit)     [a])  = cvtSV a
        sh (SBVApp (StrOp op)          args) = "(" ++ show op ++ " " ++ unwords (map cvtSV args) ++ ")"

        sh (SBVApp (RegExOp o@RegExEq{})  []) = show o
        sh (SBVApp (RegExOp o@RegExNEq{}) []) = show o

        -- Reverse and higher order functions are special
        sh (SBVApp o@(SeqOp SBVReverse{}) args) = "(" ++ firstifiedName o ++ " " ++ unwords (map cvtSV args) ++ ")"
        sh (SBVApp o@(SeqOp SBVZip{})     args) = "(" ++ firstifiedName o ++ " " ++ unwords (map cvtSV args) ++ ")"
        sh (SBVApp o@(SeqOp SBVZipWith{}) args) = "(" ++ firstifiedName o ++ " " ++ unwords (map cvtSV args) ++ ")"
        sh (SBVApp o@(SeqOp SBVReverse{}) args) = "(" ++ firstifiedName o ++ " " ++ unwords (map cvtSV args) ++ ")"
        sh (SBVApp o@(SeqOp SBVMap{})     args) = "(" ++ firstifiedName o ++ " " ++ unwords (map cvtSV args) ++ ")"
        sh (SBVApp o@(SeqOp SBVFoldl{})   args) = "(" ++ firstifiedName o ++ " " ++ unwords (map cvtSV args) ++ ")"
        sh (SBVApp o@(SeqOp SBVFoldr{})   args) = "(" ++ firstifiedName o ++ " " ++ unwords (map cvtSV args) ++ ")"
        sh (SBVApp o@(SeqOp SBVFilter{})  args) = "(" ++ firstifiedName o ++ " " ++ unwords (map cvtSV args) ++ ")"
        sh (SBVApp o@(SeqOp SBVAll{} )    args) = "(" ++ firstifiedName o ++ " " ++ unwords (map cvtSV args) ++ ")"
        sh (SBVApp o@(SeqOp SBVAny{} )    args) = "(" ++ firstifiedName o ++ " " ++ unwords (map cvtSV args) ++ ")"
        sh (SBVApp o@(SeqOp SBVConcat{})  args) = "(" ++ firstifiedName o ++ " " ++ unwords (map cvtSV args) ++ ")"

        sh (SBVApp (SeqOp op) args) = "(" ++ show op ++ " " ++ unwords (map cvtSV args) ++ ")"

        sh (SBVApp (SetOp SetEqual)      args)   = "(= "      ++ unwords (map cvtSV args) ++ ")"
        sh (SBVApp (SetOp SetMember)     [e, s]) = "(select " ++ cvtSV s ++ " " ++ cvtSV e ++ ")"
        sh (SBVApp (SetOp SetInsert)     [e, s]) = "(store "  ++ cvtSV s ++ " " ++ cvtSV e ++ " true)"
        sh (SBVApp (SetOp SetDelete)     [e, s]) = "(store "  ++ cvtSV s ++ " " ++ cvtSV e ++ " false)"
        sh (SBVApp (SetOp SetIntersect)  args)   = "(intersection " ++ unwords (map cvtSV args) ++ ")"
        sh (SBVApp (SetOp SetUnion)      args)   = "(union "        ++ unwords (map cvtSV args) ++ ")"
        sh (SBVApp (SetOp SetSubset)     args)   = "(subset "       ++ unwords (map cvtSV args) ++ ")"
        sh (SBVApp (SetOp SetDifference) args)   = "(setminus "     ++ unwords (map cvtSV args) ++ ")"
        sh (SBVApp (SetOp SetComplement) args)   = "(complement "   ++ unwords (map cvtSV args) ++ ")"

        sh (SBVApp (TupleConstructor 0)   [])    = "mkSBVTuple0"
        sh (SBVApp (TupleConstructor n)   args)  = "((as mkSBVTuple" ++ show n ++ " " ++ smtType (KTuple (map kindOf args)) ++ ") " ++ unwords (map cvtSV args) ++ ")"
        sh (SBVApp (TupleAccess      i n) [tup]) = "(proj_" ++ show i ++ "_SBVTuple" ++ show n ++ " " ++ cvtSV tup ++ ")"

        sh (SBVApp (EitherConstructor k1 k2 False) [arg]) =       dtConstructor "left_SBVEither"  [arg] (KEither k1 k2)
        sh (SBVApp (EitherConstructor k1 k2 True ) [arg]) =       dtConstructor "right_SBVEither" [arg] (KEither k1 k2)
        sh (SBVApp (EitherIs          k1 k2 False) [arg]) = '(' : dtAccessor    "left_SBVEither"  [k1]  (KEither k1 k2) ++ " " ++ cvtSV arg ++ ")"
        sh (SBVApp (EitherIs          k1 k2 True ) [arg]) = '(' : dtAccessor    "right_SBVEither" [k2]  (KEither k1 k2) ++ " " ++ cvtSV arg ++ ")"
        sh (SBVApp (EitherAccess            False) [arg]) = "(get_left_SBVEither "  ++ cvtSV arg ++ ")"
        sh (SBVApp (EitherAccess            True ) [arg]) = "(get_right_SBVEither " ++ cvtSV arg ++ ")"

        sh (SBVApp  RationalConstructor    [t, b]) = "(SBV.Rational " ++ cvtSV t ++ " " ++ cvtSV b ++ ")"

        sh (SBVApp (MaybeConstructor k False) [])    =       dtConstructor "nothing_SBVMaybe" []    (KMaybe k)
        sh (SBVApp (MaybeConstructor k True)  [arg]) =       dtConstructor "just_SBVMaybe"    [arg] (KMaybe k)
        sh (SBVApp (MaybeIs          k False) [arg]) = '(' : dtAccessor    "nothing_SBVMaybe" []    (KMaybe k) ++ " " ++ cvtSV arg ++ ")"
        sh (SBVApp (MaybeIs          k True ) [arg]) = '(' : dtAccessor    "just_SBVMaybe"    [k]   (KMaybe k) ++ " " ++ cvtSV arg ++ ")"
        sh (SBVApp MaybeAccess                [arg]) = "(get_just_SBVMaybe " ++ cvtSV arg ++ ")"

        sh (SBVApp Implies [a, b]) = "(=> " ++ cvtSV a ++ " " ++ cvtSV b ++ ")"

        sh inp@(SBVApp op args)
          | intOp, Just f <- lookup op smtOpIntTable
          = f True (map cvtSV args)
          | boolOp, Just f <- lookup op boolComps
          = f (map cvtSV args)
          | bvOp, Just f <- lookup op smtOpBVTable
          = f (any hasSign args) (map cvtSV args)
          | realOp, Just f <- lookup op smtOpRealTable
          = f (any hasSign args) (map cvtSV args)
          | ratOp, Just f <- lookup op ratOpTable
          = f (map cvtSV args)
          | fpOp, Just f <- lookup op smtOpFloatDoubleTable
          = f (any hasSign args) (map cvtSV args)
          | charOp || stringOp, Just f <- lookup op smtStringTable
          = f (map cvtSV args)
          | listOp, Just f <- lookup op smtListTable
          = f (map cvtSV args)
          | Just f <- lookup op uninterpretedTable
          = f (map cvtSV args)
          | True
          = if not (null args) && isUserSort (hd "isUserSort" args)
            then error $ unlines [ ""
                                 , "*** Cannot translate operator        : " ++ show op
                                 , "*** When applied to arguments of kind: " ++ intercalate ", " (nub (map (show . kindOf) args))
                                 , "*** Found as part of the expression  : " ++ show inp
                                 , "***"
                                 , "*** Note that uninterpreted kinds only support equality."
                                 , "*** If you believe this is in error, please report!"
                                 ]
            else error $ unlines [ ""
                                 , "*** SBV.SMT.SMTLib2.cvtExp.sh: impossible happened; can't translate: " ++ show inp
                                 , "***"
                                 , "*** Applied to arguments of type: " ++ intercalate ", " (nub (map (show . kindOf) args))
                                 , "***"
                                 , "*** This can happen if the Num instance isn't properly defined for a lifted kind."
                                 , "*** (See https://github.com/LeventErkok/sbv/issues/698 for a discussion.)"
                                 , "***"
                                 , "*** If you believe this is in error, please report!"
                                 ]
          where smtOpBVTable  = [ (Plus,          lift2   "bvadd")
                                , (Minus,         lift2   "bvsub")
                                , (Times,         lift2   "bvmul")
                                , (UNeg,          lift1B  "not"    "bvneg")
                                , (Abs,           liftAbs)
                                , (Quot,          lift2S  "bvudiv" "bvsdiv")
                                , (Rem,           lift2S  "bvurem" "bvsrem")
                                , (Equal,         eqBV)
                                , (NotEqual,      neqBV)
                                , (LessThan,      lift2S  "bvult" "bvslt")
                                , (GreaterThan,   lift2S  "bvugt" "bvsgt")
                                , (LessEq,        lift2S  "bvule" "bvsle")
                                , (GreaterEq,     lift2S  "bvuge" "bvsge")
                                ]

                -- Boolean comparisons.. SMTLib's bool type doesn't do comparisons, but Haskell does.. Sigh
                boolComps      = [ (LessThan,      blt)
                                 , (GreaterThan,   blt . swp)
                                 , (LessEq,        blq)
                                 , (GreaterEq,     blq . swp)
                                 ]
                               where blt [x, y] = "(and (not " ++ x ++ ") " ++ y ++ ")"
                                     blt xs     = error $ "SBV.SMT.SMTLib2.boolComps.blt: Impossible happened, incorrect arity (expected 2): " ++ show xs
                                     blq [x, y] = "(or (not " ++ x ++ ") " ++ y ++ ")"
                                     blq xs     = error $ "SBV.SMT.SMTLib2.boolComps.blq: Impossible happened, incorrect arity (expected 2): " ++ show xs
                                     swp [x, y] = [y, x]
                                     swp xs     = error $ "SBV.SMT.SMTLib2.boolComps.swp: Impossible happened, incorrect arity (expected 2): " ++ show xs

                smtOpRealTable =  smtIntRealShared
                               ++ [ (Quot,        lift2WM "/" "fp.div")
                                  ]

                smtOpIntTable  = smtIntRealShared
                               ++ [ (Quot,        lift2   "div")
                                  , (Rem,         lift2   "mod")
                                  ]

                smtOpFloatDoubleTable = smtIntRealShared
                                  ++ [(Quot, lift2WM "/" "fp.div")]

                smtIntRealShared  = [ (Plus,          lift2WM "+" "fp.add")
                                    , (Minus,         lift2WM "-" "fp.sub")
                                    , (Times,         lift2WM "*" "fp.mul")
                                    , (UNeg,          lift1FP "-" "fp.neg")
                                    , (Abs,           liftAbs)
                                    , (Equal,         equal)
                                    , (NotEqual,      notEqual)
                                    , (LessThan,      lift2Cmp  "<"  "fp.lt")
                                    , (GreaterThan,   lift2Cmp  ">"  "fp.gt")
                                    , (LessEq,        lift2Cmp  "<=" "fp.leq")
                                    , (GreaterEq,     lift2Cmp  ">=" "fp.geq")
                                    ]

                ratOpTable = [ (Plus,        lift2Rat "sbv.rat.plus")
                             , (Minus,       lift2Rat "sbv.rat.minus")
                             , (Times,       lift2Rat "sbv.rat.times")
                             , (UNeg,        liftRat  "sbv.rat.uneg")
                             , (Abs,         liftRat  "sbv.rat.abs")
                             , (Equal,       lift2Rat "sbv.rat.eq")
                             , (NotEqual,    lift2Rat "sbv.rat.notEq")
                             , (LessThan,    lift2Rat "sbv.rat.lt")
                             , (GreaterThan, lift2Rat "sbv.rat.lt" . swap)
                             , (LessEq,      lift2Rat "sbv.rat.leq")
                             , (GreaterEq,   lift2Rat "sbv.rat.leq" . swap)
                             ]
                        where lift2Rat o [x, y] = "(" ++ o ++ " " ++ x ++ " " ++ y ++ ")"
                              lift2Rat o sbvs   = error $ "SBV.SMTLib2.sh.lift2Rat: Unexpected arguments: "   ++ show (o, sbvs)
                              liftRat  o [x]    = "(" ++ o ++ " " ++ x ++ ")"
                              liftRat  o sbvs   = error $ "SBV.SMTLib2.sh.lift2Rat: Unexpected arguments: "   ++ show (o, sbvs)
                              swap [x, y]       = [y, x]
                              swap sbvs         = error $ "SBV.SMTLib2.sh.swap: Unexpected arguments: "   ++ show sbvs

                -- equality and comparisons are the only thing that works on uninterpreted sorts and pretty much everything else
                uninterpretedTable = [ (Equal,       lift2S "="        "="        True)
                                     , (NotEqual,    liftNS "distinct" "distinct" True)
                                     , (LessThan,    unintComp "<")
                                     , (GreaterThan, unintComp ">")
                                     , (LessEq,      unintComp "<=")
                                     , (GreaterEq,   unintComp ">=")
                                     ]

                -- For strings, equality and comparisons are the only operators
                smtStringTable = [ (Equal,       lift2S "="        "="        True)
                                 , (NotEqual,    liftNS "distinct" "distinct" True)
                                 , (LessThan,    stringCmp False "str.<")
                                 , (GreaterThan, stringCmp True  "str.<")
                                 , (LessEq,      stringCmp False "str.<=")
                                 , (GreaterEq,   stringCmp True  "str.<=")
                                 ]

                -- For lists, equality is really the only operator
                -- Likewise here, things might change for comparisons
                smtListTable = [ (Equal,       lift2S "="        "="        True)
                               , (NotEqual,    liftNS "distinct" "distinct" True)
                               , (LessThan,    seqCmp False "seq.<")
                               , (GreaterThan, seqCmp True  "seq.<")
                               , (LessEq,      seqCmp False "seq.<=")
                               , (GreaterEq,   seqCmp True  "seq.<=")
                               ]

declareFun :: SV -> SBVType -> Maybe String -> [String]
declareFun = declareName . show

-- If we have a char, we have to make sure it's and SMTLib string of length exactly one
-- If we have a rational, we have to make sure the denominator is > 0
-- Otherwise, we just declare the name
declareName :: String -> SBVType -> Maybe String -> [String]
declareName s t@(SBVType inputKS) mbCmnt = decl : restrict
  where decl        = "(declare-fun " ++ s ++ " " ++ cvtType t ++ ")" ++ maybe "" (" ; " ++) mbCmnt

        (args, result) = case inputKS of
                          [] -> error $ "SBV.declareName: Unexpected empty type for: " ++ show s
                          _  -> (init inputKS, last inputKS)

        -- Does the kind KChar and KRational *not* occur in the kind anywhere?
        charRatFree k = null $ [() | KChar <- G.universe k] ++ [() | KRational <- G.universe k]
        noCharOrRat   = charRatFree result
        needsQuant    = not $ null args

        resultVar | needsQuant = "result"
                  | True       = s

        argList   = ["a" ++ show i | (i, _) <- zip [1::Int ..] args]
        argTList  = ["(" ++ a ++ " " ++ smtType k ++ ")" | (a, k) <- zip argList args]
        resultExp = "(" ++ s ++ " " ++ unwords argList ++ ")"

        restrict | noCharOrRat = []
                 | needsQuant  =    [               "(assert (forall (" ++ unwords argTList ++ ")"
                                    ,               "                (let ((" ++ resultVar ++ " " ++ resultExp ++ "))"
                                    ]
                                 ++ (case constraints of
                                       []     ->  [ "                     true"]
                                       [x]    ->  [ "                     " ++ x]
                                       (x:xs) ->  ( "                     (and " ++ x)
                                               :  [ "                          " ++ c | c <- xs]
                                               ++ [ "                     )"])
                                 ++ [        "                )))"]
                 | True        = case constraints of
                                  []     -> []
                                  [x]    -> ["(assert " ++ x ++ ")"]
                                  (x:xs) -> ( "(assert (and " ++ x)
                                         :  [ "             " ++ c | c <- xs]
                                         ++ [ "        ))"]

        constraints = walk 0 resultVar cstr result
          where cstr KChar     nm = ["(= 1 (str.len " ++ nm ++ "))"]
                cstr KRational nm = ["(< 0 (sbv.rat.denominator " ++ nm ++ "))"]
                cstr _         _  = []

        mkAnd [] _context = []
        mkAnd [c] context = context c
        mkAnd cs  context = context $ "(and " ++ unwords cs ++ ")"

        walk :: Int -> String -> (Kind -> String -> [String]) -> Kind -> [String]
        walk _d nm f k@KBool     {}         = f k nm
        walk _d nm f k@KBounded  {}         = f k nm
        walk _d nm f k@KUnbounded{}         = f k nm
        walk _d nm f k@KReal     {}         = f k nm
        walk _d nm f k@KUserSort {}         = f k nm
        walk _d nm f k@KFloat    {}         = f k nm
        walk _d nm f k@KDouble   {}         = f k nm
        walk _d nm f k@KRational {}         = f k nm
        walk _d nm f k@KFP       {}         = f k nm
        walk _d nm f k@KChar     {}         = f k nm
        walk _d nm f k@KString   {}         = f k nm
        walk  d nm f  (KList k)
          | charRatFree k                 = []
          | True                          = let fnm   = "seq" ++ show d
                                                cstrs = walk (d+1) ("(seq.nth " ++ nm ++ " " ++ fnm ++ ")") f k
                                            in mkAnd cstrs $ \hole -> ["(forall ((" ++ fnm ++ " " ++ smtType KUnbounded ++ ")) (=> (and (>= " ++ fnm ++ " 0) (< " ++ fnm ++ " (seq.len " ++ nm ++ "))) " ++ hole ++ "))"]
        walk  d  nm f (KSet k)
          | charRatFree k                 = []
          | True                          = let fnm    = "set" ++ show d
                                                cstrs  = walk (d+1) nm (\sk snm -> ["(=> (select " ++ snm ++ " " ++ fnm ++ ") " ++ c ++ ")" | c <- f sk fnm]) k
                                            in mkAnd cstrs $ \hole -> ["(forall ((" ++ fnm ++ " " ++ smtType k ++ ")) " ++ hole ++ ")"]
        walk  d  nm  f (KTuple ks)        = let tt        = "SBVTuple" ++ show (length ks)
                                                project i = "(proj_" ++ show i ++ "_" ++ tt ++ " " ++ nm ++ ")"
                                                nmks      = [(project i, k) | (i, k) <- zip [1::Int ..] ks]
                                            in concatMap (\(n, k) -> walk (d+1) n f k) nmks
        walk  d  nm  f km@(KMaybe k)      = let n = "(get_just_SBVMaybe " ++ nm ++ ")"
                                            in  ["(=> " ++ "((_ is (just_SBVMaybe (" ++ smtType k ++ ") " ++ smtType km ++ ")) " ++ nm ++ ") " ++ c ++ ")" | c <- walk (d+1) n f k]
        walk  d  nm  f ke@(KEither k1 k2) = let n1 = "(get_left_SBVEither "  ++ nm ++ ")"
                                                n2 = "(get_right_SBVEither " ++ nm ++ ")"
                                                c1 = ["(=> " ++ "((_ is (left_SBVEither ("  ++ smtType k1 ++ ") " ++ smtType ke ++ ")) " ++ nm ++ ") " ++ c ++ ")" | c <- walk (d+1) n1 f k1]
                                                c2 = ["(=> " ++ "((_ is (right_SBVEither (" ++ smtType k2 ++ ") " ++ smtType ke ++ ")) " ++ nm ++ ") " ++ c ++ ")" | c <- walk (d+1) n2 f k2]
                                            in c1 ++ c2
        walk d  nm f  (KArray k1 k2)
          | all charRatFree [k1, k2]      = []
          | True                          = let fnm   = "array" ++ show d
                                                cstrs = walk (d+1) ("(select " ++ nm ++ " " ++ fnm ++ ")") f k2
                                            in mkAnd cstrs $ \hole -> ["(forall ((" ++ fnm ++ " " ++ smtType k1 ++ ")) " ++ hole ++ ")"]

-----------------------------------------------------------------------------------------------
-- Casts supported by SMTLib. (From: <https://smt-lib.org/theories-FloatingPoint.shtml>)
--   ; from another floating point sort
--   ((_ to_fp eb sb) RoundingMode (_ FloatingPoint mb nb) (_ FloatingPoint eb sb))
--
--   ; from real
--   ((_ to_fp eb sb) RoundingMode Real (_ FloatingPoint eb sb))
--
--   ; from signed machine integer, represented as a 2's complement bit vector
--   ((_ to_fp eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
--
--   ; from unsigned machine integer, represented as bit vector
--   ((_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
--
--   ; to unsigned machine integer, represented as a bit vector
--   ((_ fp.to_ubv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m))
--
--   ; to signed machine integer, represented as a 2's complement bit vector
--   ((_ fp.to_sbv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m))
--
--   ; to real
--   (fp.to_real (_ FloatingPoint eb sb) Real)
-----------------------------------------------------------------------------------------------

handleFPCast :: Kind -> Kind -> String -> String -> String
handleFPCast kFromIn kToIn rm input
  | kFrom == kTo
  = input
  | True
  = "(" ++ cast kFrom kTo input ++ ")"
  where addRM a s = s ++ " " ++ rm ++ " " ++ a

        kFrom = simplify kFromIn
        kTo   = simplify kToIn

        simplify KFloat  = KFP   8 24
        simplify KDouble = KFP  11 53
        simplify k       = k

        size (eb, sb) = show eb ++ " " ++ show sb

        -- To go and back from Ints, we detour through reals
        cast KUnbounded (KFP eb sb) a = "(_ to_fp " ++ size (eb, sb) ++ ") "  ++ rm ++ " (to_real " ++ a ++ ")"
        cast KFP{}      KUnbounded  a = "to_int (fp.to_real " ++ a ++ ")"

        -- To floats
        cast (KBounded False _) (KFP eb sb) a = addRM a $ "(_ to_fp_unsigned " ++ size (eb, sb) ++ ")"
        cast (KBounded True  _) (KFP eb sb) a = addRM a $ "(_ to_fp "          ++ size (eb, sb) ++ ")"
        cast KReal              (KFP eb sb) a = addRM a $ "(_ to_fp "          ++ size (eb, sb) ++ ")"
        cast KFP{}              (KFP eb sb) a = addRM a $ "(_ to_fp "          ++ size (eb, sb) ++ ")"

        -- From float/double
        cast KFP{} (KBounded False m) a = addRM a $ "(_ fp.to_ubv " ++ show m ++ ")"
        cast KFP{} (KBounded True  m) a = addRM a $ "(_ fp.to_sbv " ++ show m ++ ")"

        -- To real
        cast KFP{} KReal a = "fp.to_real" ++ " " ++ a

        -- Nothing else should come up:
        cast f  d  _ = error $ "SBV.SMTLib2: Unexpected FPCast from: " ++ show f ++ " to " ++ show d

rot :: String -> Int -> SV -> String
rot o c x = "((_ " ++ o ++ " " ++ show c ++ ") " ++ cvtSV x ++ ")"

shft :: String -> String -> SV -> SV -> String
shft oW oS x c = "(" ++ o ++ " " ++ cvtSV x ++ " " ++ cvtSV c ++ ")"
   where o = if hasSign x then oS else oW

-- Various casts
handleKindCast :: Bool -> Kind -> Kind -> String -> String
handleKindCast hasInt2bv kFrom kTo a
  | kFrom == kTo
  = a
  | True
  = case kFrom of
      KBounded s m -> case kTo of
                        KBounded _ n -> fromBV (if s then signExtend else zeroExtend) m n
                        KUnbounded   -> b2i s m
                        _            -> tryFPCast

      KUnbounded   -> case kTo of
                        KReal        -> "(to_real " ++ a ++ ")"
                        KBounded _ n -> i2b n
                        _            -> tryFPCast

      KReal        -> case kTo of
                        KUnbounded   -> "(to_int " ++ a ++ ")"
                        _            -> tryFPCast

      _            -> tryFPCast

  where -- See if we can push this down to a float-cast, using sRNE. This happens if one of the kinds is a float/double.
        -- Otherwise complain
        tryFPCast
          | any (\k -> isFloat k || isDouble k) [kFrom, kTo]
          = handleFPCast kFrom kTo (smtRoundingMode RoundNearestTiesToEven) a
          | True
          = error $ "SBV.SMTLib2: Unexpected cast from: " ++ show kFrom ++ " to " ++ show kTo

        fromBV upConv m n
         | n > m  = upConv  (n - m)
         | m == n = a
         | True   = extract (n - 1)

        b2i False _ = "(bv2nat " ++ a ++ ")"
        b2i True  1 = "(ite (= " ++ a ++ " #b0) 0 (- 1))"
        b2i True  m = "(ite (= " ++ msb ++ " #b0" ++ ") " ++ ifPos ++ " " ++ ifNeg ++ ")"
          where offset :: Integer
                offset = 2^(m-1)
                rest   = extract (m - 2)

                msb    = let top = show (m-1) in "((_ extract " ++ top ++ " " ++ top ++ ") " ++ a ++ ")"
                ifPos  = "(bv2nat " ++ rest ++")"
                ifNeg  = "(- " ++ ifPos ++ " " ++ show offset ++ ")"

        signExtend i = "((_ sign_extend " ++ show i ++  ") "  ++ a ++ ")"
        zeroExtend i = "((_ zero_extend " ++ show i ++  ") "  ++ a ++ ")"
        extract    i = "((_ extract "     ++ show i ++ " 0) " ++ a ++ ")"

        -- Some solvers support int2bv, but not all. So, we use a capability to determine.
        --
        -- NB. The "manual" implementation works regardless n < 0 or not, because the first thing we
        -- do is to compute "reduced" to bring it down to the correct range. It also works
        -- regardless were mapping to signed or unsigned bit-vector; because the representation
        -- is the same.
        i2b n
          | hasInt2bv
          = "((_ int2bv " ++ show n ++ ") " ++ a ++ ")"
          | True
          = "(let (" ++ reduced ++ ") (let (" ++ defs ++ ") " ++ body ++ "))"
          where b i      = show (bit i :: Integer)
                reduced  = "(__a (mod " ++ a ++ " " ++ b n ++ "))"
                mkBit 0  = "(__a0 (ite (= (mod __a 2) 0) #b0 #b1))"
                mkBit i  = "(__a" ++ show i ++ " (ite (= (mod (div __a " ++ b i ++ ") 2) 0) #b0 #b1))"
                defs     = unwords (map mkBit [0 .. n - 1])
                body     = foldr1 (\c r -> "(concat " ++ c ++ " " ++ r ++ ")") ["__a" ++ show i | i <- [n-1, n-2 .. 0]]

-- Translation of pseudo-booleans, in case the solver supports them
handlePB :: PBOp -> [String] -> String
handlePB (PB_AtMost  k) args = "((_ at-most "  ++ show k                                             ++ ") " ++ unwords args ++ ")"
handlePB (PB_AtLeast k) args = "((_ at-least " ++ show k                                             ++ ") " ++ unwords args ++ ")"
handlePB (PB_Exactly k) args = "((_ pbeq "     ++ unwords (map show (k : replicate (length args) 1)) ++ ") " ++ unwords args ++ ")"
handlePB (PB_Eq cs   k) args = "((_ pbeq "     ++ unwords (map show (k : cs))                        ++ ") " ++ unwords args ++ ")"
handlePB (PB_Le cs   k) args = "((_ pble "     ++ unwords (map show (k : cs))                        ++ ") " ++ unwords args ++ ")"
handlePB (PB_Ge cs   k) args = "((_ pbge "     ++ unwords (map show (k : cs))                        ++ ") " ++ unwords args ++ ")"

-- Translation of pseudo-booleans, in case the solver does *not* support them
reducePB :: PBOp -> [String] -> String
reducePB op args = case op of
                     PB_AtMost  k -> "(<= " ++ addIf (repeat 1) ++ " " ++ show k ++ ")"
                     PB_AtLeast k -> "(>= " ++ addIf (repeat 1) ++ " " ++ show k ++ ")"
                     PB_Exactly k -> "(=  " ++ addIf (repeat 1) ++ " " ++ show k ++ ")"
                     PB_Le cs   k -> "(<= " ++ addIf cs         ++ " " ++ show k ++ ")"
                     PB_Ge cs   k -> "(>= " ++ addIf cs         ++ " " ++ show k ++ ")"
                     PB_Eq cs   k -> "(=  " ++ addIf cs         ++ " " ++ show k ++ ")"

  where addIf :: [Int] -> String
        addIf cs = "(+ " ++ unwords ["(ite " ++ a ++ " " ++ show c ++ " 0)" | (a, c) <- zip args cs] ++ ")"

-- | Translate an option setting to SMTLib. Note the SetLogic/SetInfo discrepancy.
setSMTOption :: SMTConfig -> SMTOption -> String
setSMTOption cfg = set
  where set (DiagnosticOutputChannel   f) = opt   [":diagnostic-output-channel",   show f]
        set (ProduceAssertions         b) = opt   [":produce-assertions",          smtBool b]
        set (ProduceAssignments        b) = opt   [":produce-assignments",         smtBool b]
        set (ProduceProofs             b) = opt   [":produce-proofs",              smtBool b]
        set (ProduceInterpolants       b) = opt   [":produce-interpolants",        smtBool b]
        set (ProduceUnsatAssumptions   b) = opt   [":produce-unsat-assumptions",   smtBool b]
        set (ProduceUnsatCores         b) = opt   [":produce-unsat-cores",         smtBool b]
        set (ProduceAbducts            b) = opt   [":produce-abducts",             smtBool b]
        set (RandomSeed                i) = opt   [":random-seed",                 show i]
        set (ReproducibleResourceLimit i) = opt   [":reproducible-resource-limit", show i]
        set (SMTVerbosity              i) = opt   [":verbosity",                   show i]
        set (OptionKeyword          k as) = opt   (k : as)
        set (SetLogic                  l) = logic l
        set (SetInfo                k as) = info  (k : as)
        set (SetTimeOut                i) = opt   $ timeOut i

        opt   xs = "(set-option " ++ unwords xs ++ ")"
        info  xs = "(set-info "   ++ unwords xs ++ ")"

        logic Logic_NONE = "; NB. not setting the logic per user request of Logic_NONE"
        logic l          = "(set-logic " ++ show l ++ ")"

        -- timeout is not standard. We distinguish between CVC/Z3. All else follows z3
        -- The value is in milliseconds, which is how z3/CVC interpret it
        timeOut i = case name (solver cfg) of
                     CVC4 -> [":tlimit",  show i]
                     CVC5 -> [":tlimit",  show i]
                     _    -> [":timeout", show i]

        -- SMTLib's True/False is spelled differently than Haskell's.
        smtBool :: Bool -> String
        smtBool True  = "true"
        smtBool False = "false"
