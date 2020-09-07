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

{-# LANGUAGE PatternGuards #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.SMT.SMTLib2(cvt, cvtInc) where

import Data.List  (intercalate, partition, nub, sort)
import Data.Maybe (listToMaybe, fromMaybe, catMaybes)

import qualified Data.Foldable as F (toList)
import qualified Data.Map.Strict      as M
import qualified Data.IntMap.Strict   as IM
import           Data.Set             (Set)
import qualified Data.Set             as Set

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic (QueryContext(..), SetOp(..))
import Data.SBV.Core.Kind (smtType, needsFlattening)
import Data.SBV.SMT.Utils
import Data.SBV.Control.Types

import Data.SBV.Utils.PrettyNum (smtRoundingMode, cvToSMTLib)

tbd :: String -> a
tbd e = error $ "SBV.SMTLib2: Not-yet-supported: " ++ e

-- | Translate a problem into an SMTLib2 script
cvt :: SMTLibConverter [String]
cvt ctx kindInfo isSat comments (inputs, trackerVars) skolemInps consts tbls arrs uis axs (SBVPgm asgnsSeq) cstrs out cfg = pgm
  where hasInteger     = KUnbounded `Set.member` kindInfo
        hasReal        = KReal      `Set.member` kindInfo
        hasFloat       = KFloat     `Set.member` kindInfo
        hasString      = KString    `Set.member` kindInfo
        hasChar        = KChar      `Set.member` kindInfo
        hasDouble      = KDouble    `Set.member` kindInfo
        hasRounding    = not $ null [s | (s, _) <- usorts, s == "RoundingMode"]
        hasBVs         = hasChar || not (null [() | KBounded{} <- Set.toList kindInfo])   -- Remember, characters map to Word8
        usorts         = [(s, dt) | KUserSort s dt <- Set.toList kindInfo]
        trueUSorts     = [s | (s, _) <- usorts, s /= "RoundingMode"]
        tupleArities   = findTupleArities kindInfo
        hasNonBVArrays = (not . null) [() | (_, (_, (k1, k2), _)) <- arrs, not (isBounded k1 && isBounded k2)]
        hasArrayInits  = (not . null) [() | (_, (_, _, ArrayFree (Just _))) <- arrs]
        hasList        = any isList kindInfo
        hasSets        = any isSet kindInfo
        hasTuples      = not . null $ tupleArities
        hasEither      = any isEither kindInfo
        hasMaybe       = any isMaybe  kindInfo
        rm             = roundingMode cfg
        solverCaps     = capabilities (solver cfg)

        -- Is there a reason why we can't handle this problem?
        -- NB. There's probably a lot more checking we can do here, but this is a start:
        doesntHandle = listToMaybe [nope w | (w, have, need) <- checks, need && not have]
           where checks = [ ("data types",     supportsDataTypes  solverCaps, hasTuples || hasEither || hasMaybe)
                          , ("set operations", supportsSets       solverCaps, hasSets)
                          , ("bit vectors",    supportsBitVectors solverCaps, hasBVs)
                          ]

                 nope w = [ "***     Given problem requires support for " ++ w
                          , "***     But the chosen solver (" ++ show (name (solver cfg)) ++ ") doesn't support this feature."
                          ]

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

           | hasInteger || hasReal || not (null trueUSorts) || hasNonBVArrays || hasTuples || hasEither || hasMaybe || hasSets || hasList || hasString || hasArrayInits
           = let why | hasInteger            = "has unbounded values"
                     | hasReal               = "has algebraic reals"
                     | not (null trueUSorts) = "has user-defined sorts"
                     | hasNonBVArrays        = "has non-bitvector arrays"
                     | hasTuples             = "has tuples"
                     | hasEither             = "has either type"
                     | hasMaybe              = "has maybe type"
                     | hasSets               = "has sets"
                     | hasList               = "has lists"
                     | hasString             = "has strings"
                     | hasArrayInits         = "has array initializers"
                     | True                  = "cannot determine the SMTLib-logic to use"
             in ["(set-logic ALL) ; "  ++ why ++ ", using catch-all."]

           | hasDouble || hasFloat || hasRounding
           = if not (null foralls)
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
          where qs  | null foralls && null axs = "QF_"  -- axioms are likely to contain quantifiers
                    | True                     = ""
                as  | null arrs                = ""
                    | True                     = "A"
                ufs | null uis && null tbls    = ""     -- we represent tables as UFs
                    | True                     = "UF"

        -- SBV always requires the production of models!
        getModels   = "(set-option :produce-models true)"
                    : concat [flattenConfig | any needsFlattening kindInfo, Just flattenConfig <- [supportsFlattenedModels solverCaps]]

        -- process all other settings we're given. If an option cannot be repeated, we only take the last one.
        userSettings = map setSMTOption $ filter (not . isLogic) $ foldr comb [] $ solverSetOptions cfg
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

        pgm  =  map ("; " ++) comments
             ++ settings
             ++ [ "; --- uninterpreted sorts ---" ]
             ++ concatMap declSort usorts
             ++ [ "; --- tuples ---" ]
             ++ concatMap declTuple tupleArities
             ++ [ "; --- sums ---" ]
             ++ (if containsSum   kindInfo then declSum   else [])
             ++ (if containsMaybe kindInfo then declMaybe else [])
             ++ [ "; --- literal constants ---" ]
             ++ concatMap (declConst cfg) consts
             ++ [ "; --- skolem constants ---" ]
             ++ [ "(declare-fun " ++ show s ++ " " ++ svFunType ss s ++ ")" ++ userName s | Right (s, ss) <- skolemInps]
             ++ [ "; --- optimization tracker variables ---" | not (null trackerVars) ]
             ++ [ "(declare-fun " ++ show s ++ " " ++ svFunType [] s ++ ") ; tracks " ++ nm | (s, nm) <- trackerVars]
             ++ [ "; --- constant tables ---" ]
             ++ concatMap (uncurry (:) . constTable) constTables
             ++ [ "; --- skolemized tables ---" ]
             ++ map (skolemTable (unwords (map svType foralls))) skolemTables
             ++ [ "; --- arrays ---" ]
             ++ concat arrayConstants
             ++ [ "; --- uninterpreted constants ---" ]
             ++ concatMap declUI uis
             ++ [ "; --- user given axioms ---" ]
             ++ map declAx axs
             ++ [ "; --- formula ---" ]

             ++ concatMap (declDef cfg skolemMap tableMap) preQuantifierAssigns
             ++ ["(assert (forall (" ++ intercalate "\n                 "
                                        ["(" ++ show s ++ " " ++ svType s ++ ")" | s <- foralls] ++ ")"
                | not (null foralls)
                ]
             ++ concatMap mkAssign postQuantifierAssigns

             ++ concat arrayDelayeds

             ++ concat arraySetups

             ++ delayedAsserts delayedEqualities

             ++ finalAssert

        -- identify the assignments that can come before the first quantifier
        (preQuantifierAssigns, postQuantifierAssigns)
           | null foralls
           = ([], asgns)  -- the apparent "switch" here is OK; rest of the code works correctly if there are no foralls.
           | True
           = span pre asgns
           where first      = nodeId (minimum foralls)
                 pre (s, _) = nodeId s < first

                 nodeId (SV _ n) = n

        noOfCloseParens
          | null foralls = 0
          | True         = length postQuantifierAssigns + 2 + (if null delayedEqualities then 0 else 1)

        foralls    = [s | Left s <- skolemInps]
        forallArgs = concatMap ((" " ++) . show) foralls

        (constTables, skolemTables) = ([(t, d) | (t, Left d) <- allTables], [(t, d) | (t, Right d) <- allTables])
        allTables = [(t, genTableData rm skolemMap (not (null foralls), forallArgs) (map fst consts) t) | t <- tbls]
        (arrayConstants, arrayDelayeds, arraySetups) = unzip3 $ map (declArray cfg (not (null foralls)) consts skolemMap) arrs
        delayedEqualities = concatMap snd skolemTables

        delayedAsserts []              = []
        delayedAsserts ds@(deH : deTs)
          | null foralls = map (\s -> "(assert " ++ s ++ ")") ds
          | True         = map letShift (("(and " ++ deH) : map (align 5) deTs)

        letShift = align 12

        finalAssert
          | null foralls && noConstraints
          = []
          | null foralls
          =    map (\(attr, v) -> "(assert "      ++ addAnnotations attr (mkLiteral v) ++ ")") hardAsserts
            ++ map (\(attr, v) -> "(assert-soft " ++ addAnnotations attr (mkLiteral v) ++ ")") softAsserts
          | not (null namedAsserts)
          = error $ intercalate "\n" [ "SBV: Constraints with attributes and quantifiers cannot be mixed!"
                                     , "   Quantified variables: " ++ unwords (map show foralls)
                                     , "   Named constraints   : " ++ intercalate ", " (map show namedAsserts)
                                     ]
          | not (null softAsserts)
          = error $ intercalate "\n" [ "SBV: Soft constraints and quantifiers cannot be mixed!"
                                     , "   Quantified variables: " ++ unwords (map show foralls)
                                     , "   Soft constraints    : " ++ intercalate ", " (map show softAsserts)
                                     ]
          | True
          = [impAlign (letShift combined) ++ replicate noOfCloseParens ')']
          where mkLiteral (Left  v) =            cvtSV skolemMap v
                mkLiteral (Right v) = "(not " ++ cvtSV skolemMap v ++ ")"

                (noConstraints, assertions) = finalAssertions

                namedAsserts = [findName attrs | (_, attrs, _) <- assertions, not (null attrs)]
                 where findName attrs = fromMaybe "<anonymous>" (listToMaybe [nm | (":named", nm) <- attrs])

                hardAsserts, softAsserts :: [([(String, String)], Either SV SV)]
                hardAsserts = [(attr, v) | (False, attr, v) <- assertions]
                softAsserts = [(attr, v) | (True,  attr, v) <- assertions]

                combined = case lits of
                             []               -> "true"
                             [x]              -> mkLiteral x
                             xs  | any bad xs -> "false"
                                 | True       -> "(and " ++ unwords (map mkLiteral xs) ++ ")"
                  where lits = filter (not . redundant) $ nub (sort (map snd hardAsserts))
                        redundant (Left v)  = v == trueSV
                        redundant (Right v) = v == falseSV
                        bad (Left  v) = v == falseSV
                        bad (Right v) = v == trueSV

        impAlign s
          | null delayedEqualities = s
          | True                   = "     " ++ s

        align n s = replicate n ' ' ++ s

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

        skolemMap = M.fromList [(s, ss) | Right (s, ss) <- skolemInps, not (null ss)]
        tableMap  = IM.fromList $ map mkConstTable constTables ++ map mkSkTable skolemTables
          where mkConstTable (((t, _, _), _), _) = (t, "table" ++ show t)
                mkSkTable    (((t, _, _), _), _) = (t, "table" ++ show t ++ forallArgs)
        asgns = F.toList asgnsSeq

        mkAssign a
          | null foralls = declDef cfg skolemMap tableMap a
          | True         = [letShift (mkLet a)]

        mkLet (s, SBVApp (Label m) [e]) = "(let ((" ++ show s ++ " " ++ cvtSV                skolemMap          e ++ ")) ; " ++ m
        mkLet (s, e)                    = "(let ((" ++ show s ++ " " ++ cvtExp solverCaps rm skolemMap tableMap e ++ "))"

        userNameMap = M.fromList (map snd inputs)
        userName s = case M.lookup s userNameMap of
                        Just u  | show s /= u -> " ; tracks user variable " ++ show u
                        _ -> ""

-- | Declare new sorts
declSort :: (String, Maybe [String]) -> [String]
declSort (s, _)
  | s == "RoundingMode" -- built-in-sort; so don't declare.
  = []
declSort (s, Nothing) = ["(declare-sort " ++ s ++ " 0)  ; N.B. Uninterpreted sort." ]
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

-- | Convert in a query context.
-- NB. We do not store everything in @newKs@ below, but only what we need
-- to do as an extra in the incremental context. See `Data.SBV.Core.Symbolic.registerKind`
-- for a list of what we include, in case something doesn't show up
-- and you need it!
cvtInc :: SMTLibIncConverter [String]
cvtInc inps newKs consts arrs tbls uis (SBVPgm asgnsSeq) cstrs cfg =
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
            ++ map declInp inps
            -- arrays
            ++ concat arrayConstants
            -- uninterpreteds
            ++ concatMap declUI uis
            -- table declarations
            ++ tableDecls
            -- expressions
            ++ concatMap (declDef cfg skolemMap tableMap) (F.toList asgnsSeq)
            -- delayed equalities
            ++ concat arrayDelayeds
            -- table setups
            ++ concat tableAssigns
            -- array setups
            ++ concat arraySetups
            -- extra constraints
            ++ map (\(isSoft, attr, v) -> "(assert" ++ (if isSoft then "-soft " else " ") ++ addAnnotations attr (cvtSV skolemMap v) ++ ")") (F.toList cstrs)
  where -- NB. The below setting of skolemMap to empty is OK, since we do
        -- not support queries in the context of skolemized variables
        skolemMap = M.empty

        rm = roundingMode cfg

        newKinds = Set.toList newKs

        declInp (s, _) = "(declare-fun " ++ show s ++ " () " ++ svType s ++ ")"

        (arrayConstants, arrayDelayeds, arraySetups) = unzip3 $ map (declArray cfg False consts skolemMap) arrs

        allTables = [(t, either id id (genTableData rm skolemMap (False, []) (map fst consts) t)) | t <- tbls]
        (tableDecls, tableAssigns) = unzip $ map constTable allTables

        tableMap  = IM.fromList $ map mkTable allTables
          where mkTable (((t, _, _), _), _) = (t, "table" ++ show t)

        -- If we need flattening in models, do emit the required lines if preset
        settings
          | any needsFlattening newKinds
          = concat (catMaybes [supportsFlattenedModels solverCaps])
          | True
          = []
          where solverCaps = capabilities (solver cfg)

declDef :: SMTConfig -> SkolemMap -> TableMap -> (SV, SBVExpr) -> [String]
declDef cfg skolemMap tableMap (s, expr) =
        case expr of
          SBVApp  (Label m) [e] -> defineFun cfg (s, cvtSV          skolemMap          e) (Just m)
          e                     -> defineFun cfg (s, cvtExp caps rm skolemMap tableMap e) Nothing
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

declUI :: (String, SBVType) -> [String]
declUI (i, t) = ["(declare-fun " ++ i ++ " " ++ cvtType t ++ ")"]

-- NB. We perform no check to as to whether the axiom is meaningful in any way.
declAx :: (String, [String]) -> String
declAx (nm, ls) = (";; -- user given axiom: " ++ nm ++ "\n") ++ intercalate "\n" ls

constTable :: (((Int, Kind, Kind), [SV]), [String]) -> (String, [String])
constTable (((i, ak, rk), _elts), is) = (decl, zipWith wrap [(0::Int)..] is ++ setup)
  where t       = "table" ++ show i
        decl    = "(declare-fun " ++ t ++ " (" ++ smtType ak ++ ") " ++ smtType rk ++ ")"

        -- Arrange for initializers
        mkInit idx   = "table" ++ show i ++ "_initializer_" ++ show (idx :: Int)
        initializer  = "table" ++ show i ++ "_initializer"

        wrap index s = "(define-fun " ++ mkInit index ++ " () Bool " ++ s ++ ")"

        lis  = length is

        setup
          | lis == 0       = [ "(define-fun " ++ initializer ++ " () Bool true) ; no initializiation needed"
                             ]
          | lis == 1       = [ "(define-fun " ++ initializer ++ " () Bool " ++ mkInit 0 ++ ")"
                             , "(assert " ++ initializer ++ ")"
                             ]
          | True           = [ "(define-fun " ++ initializer ++ " () Bool (and " ++ unwords (map mkInit [0..lis - 1]) ++ "))"
                             , "(assert " ++ initializer ++ ")"
                             ]

skolemTable :: String -> (((Int, Kind, Kind), [SV]), [String]) -> String
skolemTable qsIn (((i, ak, rk), _elts), _) = decl
  where qs   = if null qsIn then "" else qsIn ++ " "
        t    = "table" ++ show i
        decl = "(declare-fun " ++ t ++ " (" ++ qs ++ smtType ak ++ ") " ++ smtType rk ++ ")"

-- Left if all constants, Right if otherwise
genTableData :: RoundingMode -> SkolemMap -> (Bool, String) -> [SV] -> ((Int, Kind, Kind), [SV]) -> Either [String] [String]
genTableData rm skolemMap (_quantified, args) consts ((i, aknd, _), elts)
  | null post = Left  (map (topLevel . snd) pre)
  | True      = Right (map (nested   . snd) (pre ++ post))
  where ssv = cvtSV skolemMap
        (pre, post) = partition fst (zipWith mkElt elts [(0::Int)..])
        t           = "table" ++ show i

        mkElt x k   = (isReady, (idx, ssv x))
          where idx = cvtCV rm (mkConstCV aknd k)
                isReady = x `Set.member` constsSet

        topLevel (idx, v) = "(= (" ++ t ++ " " ++ idx ++ ") " ++ v ++ ")"
        nested   (idx, v) = "(= (" ++ t ++ args ++ " " ++ idx ++ ") " ++ v ++ ")"

        constsSet = Set.fromList consts

-- TODO: We currently do not support non-constant arrays when quantifiers are present, as
-- we might have to skolemize those. Implement this properly.
-- The difficulty is with the Mutate/Merge: We have to postpone an init if
-- the components are themselves postponed, so this cannot be implemented as a simple map.
declArray :: SMTConfig -> Bool -> [(SV, CV)] -> SkolemMap -> (Int, ArrayInfo) -> ([String], [String], [String])
declArray cfg quantified consts skolemMap (i, (_, (aKnd, bKnd), ctx)) = (adecl : zipWith wrap [(0::Int)..] (map snd pre), zipWith wrap [lpre..] (map snd post), setup)
  where constNames = map fst consts
        topLevel = not quantified || case ctx of
                                       ArrayFree mbi      -> maybe True (`elem` constNames) mbi
                                       ArrayMutate _ a b  -> all (`elem` constNames) [a, b]
                                       ArrayMerge c _ _   -> c `elem` constNames
        (pre, post) = partition fst ctxInfo
        nm = "array_" ++ show i

        ssv sv
         | topLevel || sv `elem` constNames
         = cvtSV skolemMap sv
         | True
         = tbd "Non-constant array initializer in a quantified context"

        atyp  = "(Array " ++ smtType aKnd ++ " " ++ smtType bKnd ++ ")"

        adecl = case ctx of
                  ArrayFree (Just v) -> "(define-fun "  ++ nm ++ " () " ++ atyp ++ " ((as const " ++ atyp ++ ") " ++ constInit v ++ "))"
                  _                  -> "(declare-fun " ++ nm ++ " () " ++ atyp ++                                                  ")"

        -- CVC4 chokes if the initializer is not a constant. (Z3 is ok with it.) So, print it as
        -- a constant if we have it in the constants; otherwise, we merely print it and hope for the best.
        constInit v = case v `lookup` consts of
                        Nothing -> ssv v                      -- Z3 will work, CVC4 will choke. Others don't even support this.
                        Just c  -> cvtCV (roundingMode cfg) c -- Z3 and CVC4 will work. Other's don't support this.

        ctxInfo = case ctx of
                    ArrayFree _       -> []
                    ArrayMutate j a b -> [(all (`elem` constNames) [a, b], "(= " ++ nm ++ " (store array_" ++ show j ++ " " ++ ssv a ++ " " ++ ssv b ++ "))")]
                    ArrayMerge  t j k -> [(t `elem` constNames,            "(= " ++ nm ++ " (ite " ++ ssv t ++ " array_" ++ show j ++ " array_" ++ show k ++ "))")]

        -- Arrange for initializers
        mkInit idx    = "array_" ++ show i ++ "_initializer_" ++ show (idx :: Int)
        initializer   = "array_" ++ show i ++ "_initializer"

        wrap index s = "(define-fun " ++ mkInit index ++ " () Bool " ++ s ++ ")"

        lpre          = length pre
        lAll          = lpre + length post

        setup
          | lAll == 0      = [ "(define-fun " ++ initializer ++ " () Bool true) ; no initializiation needed" | not quantified]
          | lAll == 1      = [ "(define-fun " ++ initializer ++ " () Bool " ++ mkInit 0 ++ ")"
                             , "(assert " ++ initializer ++ ")"
                             ]
          | True           = [ "(define-fun " ++ initializer ++ " () Bool (and " ++ unwords (map mkInit [0..lAll - 1]) ++ "))"
                             , "(assert " ++ initializer ++ ")"
                             ]

svType :: SV -> String
svType s = smtType (kindOf s)

svFunType :: [SV] -> SV -> String
svFunType ss s = "(" ++ unwords (map svType ss) ++ ") " ++ svType s

cvtType :: SBVType -> String
cvtType (SBVType []) = error "SBV.SMT.SMTLib2.cvtType: internal: received an empty type!"
cvtType (SBVType xs) = "(" ++ unwords (map smtType body) ++ ") " ++ smtType ret
  where (body, ret) = (init xs, last xs)

type SkolemMap = M.Map SV [SV]
type TableMap  = IM.IntMap String

-- Present an SV; inline true/false as needed
cvtSV :: SkolemMap -> SV -> String
cvtSV skolemMap s@(SV _ (NodeId n))
  | Just ss <- s `M.lookup` skolemMap
  = "(" ++ show s ++ concatMap ((" " ++) . show) ss ++ ")"
  | s == trueSV
  = "true"
  | s == falseSV
  = "false"
  | True
  = 's' : show n

cvtCV :: RoundingMode -> CV -> String
cvtCV = cvToSMTLib

getTable :: TableMap -> Int -> String
getTable m i
  | Just tn <- i `IM.lookup` m = tn
  | True                       = "table" ++ show i  -- constant tables are always named this way

cvtExp :: SolverCapabilities -> RoundingMode -> SkolemMap -> TableMap -> SBVExpr -> String
cvtExp caps rm skolemMap tableMap expr@(SBVApp _ arguments) = sh expr
  where ssv = cvtSV skolemMap

        supportsPB = supportsPseudoBooleans caps

        hasDistinct = supportsDistinct caps

        bvOp     = all isBounded   arguments
        intOp    = any isUnbounded arguments
        realOp   = any isReal      arguments
        doubleOp = any isDouble    arguments
        floatOp  = any isFloat     arguments
        boolOp   = all isBoolean   arguments
        charOp   = any isChar      arguments
        stringOp = any isString    arguments
        listOp   = any isList      arguments

        bad | intOp = error $ "SBV.SMTLib2: Unsupported operation on unbounded integers: " ++ show expr
            | True  = error $ "SBV.SMTLib2: Unsupported operation on real values: " ++ show expr

        ensureBVOrBool = bvOp || boolOp || bad
        ensureBV       = bvOp || bad

        addRM s = s ++ " " ++ smtRoundingMode rm

        -- lift a binary op
        lift2  o _ [x, y] = "(" ++ o ++ " " ++ x ++ " " ++ y ++ ")"
        lift2  o _ sbvs   = error $ "SBV.SMTLib2.sh.lift2: Unexpected arguments: "   ++ show (o, sbvs)

        -- lift an arbitrary arity operator
        liftN o _ xs = "(" ++ o ++ " " ++ unwords xs ++ ")"

        -- lift a binary operation with rounding-mode added; used for floating-point arithmetic
        lift2WM o fo | doubleOp || floatOp = lift2 (addRM fo)
                     | True                = lift2 o

        lift1FP o fo | doubleOp || floatOp = lift1 fo
                     | True                = lift1 o

        liftAbs sgned args | doubleOp || floatOp = lift1 "fp.abs" sgned args
                           | intOp               = lift1 "abs"    sgned args
                           | bvOp, sgned         = mkAbs (head args) "bvslt" "bvneg"
                           | bvOp                = head args
                           | True                = mkAbs (head args) "<"     "-"
          where mkAbs x cmp neg = "(ite " ++ ltz ++ " " ++ nx ++ " " ++ x ++ ")"
                  where ltz = "(" ++ cmp ++ " " ++ x ++ " " ++ z ++ ")"
                        nx  = "(" ++ neg ++ " " ++ x ++ ")"
                        z   = cvtCV rm (mkConstCV (kindOf (head arguments)) (0::Integer))

        lift2B bOp vOp
          | boolOp = lift2 bOp
          | True   = lift2 vOp

        lift1B bOp vOp
          | boolOp = lift1 bOp
          | True   = lift1 vOp

        eqBV  = lift2 "="
        neqBV = liftN "distinct"

        equal sgn sbvs
          | doubleOp = lift2 "fp.eq" sgn sbvs
          | floatOp  = lift2 "fp.eq" sgn sbvs
          | True     = lift2 "="     sgn sbvs

        notEqual sgn sbvs
          | doubleOp || floatOp || not hasDistinct = liftP sbvs
          | True                                   = liftN "distinct" sgn sbvs
          where liftP [_, _] = "(not " ++ equal sgn sbvs ++ ")"
                liftP args   = "(and " ++ unwords (walk args) ++ ")"

                walk []     = []
                walk (e:es) = map (\e' -> liftP [e, e']) es ++ walk es

        lift2S oU oS sgn = lift2 (if sgn then oS else oU) sgn
        liftNS oU oS sgn = liftN (if sgn then oS else oU) sgn

        lift2Cmp o fo | doubleOp || floatOp = lift2 fo
                      | True                = lift2 o

        unintComp o [a, b]
          | KUserSort s (Just _) <- kindOf (head arguments)
          = let idx v = "(" ++ s ++ "_constrIndex " ++ v ++ ")" in "(" ++ o ++ " " ++ idx a ++ " " ++ idx b ++ ")"
        unintComp o sbvs = error $ "SBV.SMT.SMTLib2.sh.unintComp: Unexpected arguments: "   ++ show (o, sbvs, map kindOf arguments)

        -- NB. String comparisons are currently not supported by Z3; but will be with the new logic.
        stringCmp swap o [a, b]
          | KString <- kindOf (head arguments)
          = let [a1, a2] | swap = [b, a]
                         | True = [a, b]
            in "(" ++ o ++ " " ++ a1 ++ " " ++ a2 ++ ")"
        stringCmp _ o sbvs = error $ "SBV.SMT.SMTLib2.sh.stringCmp: Unexpected arguments: " ++ show (o, sbvs)

        -- NB. Likewise for sequences
        seqCmp swap o [a, b]
          | KList{} <- kindOf (head arguments)
          = let [a1, a2] | swap = [b, a]
                         | True = [a, b]
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
        dtConstructor fld args res = "((as " ++ fld ++ " " ++ smtType res ++ ") " ++ unwords (map ssv args) ++ ")"

        -- Similarly, we fully qualify the accessors with their types to work around type checking issues
        -- Unfortunately, z3 and CVC4 are behaving differently, so we tie this ascription to a solver capability.
        dtAccessor fld params res
           | supportsDirectAccessors caps = dResult
           | True                         = aResult
          where dResult = "(_ is " ++ fld ++ ")"
                ps      = " (" ++ unwords (map smtType params) ++ ") "
                aResult = "(_ is (" ++ fld ++ ps ++ smtType res ++ "))"

        sh (SBVApp Ite [a, b, c]) = "(ite " ++ ssv a ++ " " ++ ssv b ++ " " ++ ssv c ++ ")"

        sh (SBVApp (LkUp (t, aKnd, _, l) i e) [])
          | needsCheck = "(ite " ++ cond ++ ssv e ++ " " ++ lkUp ++ ")"
          | True       = lkUp
          where needsCheck = case aKnd of
                              KBool         -> (2::Integer) > fromIntegral l
                              KBounded _ n  -> (2::Integer)^n > fromIntegral l
                              KUnbounded    -> True
                              KReal         -> error "SBV.SMT.SMTLib2.cvtExp: unexpected real valued index"
                              KFloat        -> error "SBV.SMT.SMTLib2.cvtExp: unexpected float valued index"
                              KDouble       -> error "SBV.SMT.SMTLib2.cvtExp: unexpected double valued index"
                              KChar         -> error "SBV.SMT.SMTLib2.cvtExp: unexpected char valued index"
                              KString       -> error "SBV.SMT.SMTLib2.cvtExp: unexpected string valued index"
                              KList k       -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected list valued: " ++ show k
                              KSet  k       -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected set valued: " ++ show k
                              KTuple k      -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected tuple valued: " ++ show k
                              KMaybe k      -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected maybe valued: " ++ show k
                              KEither k1 k2 -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected sum valued: " ++ show (k1, k2)
                              KUserSort s _ -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected uninterpreted valued index: " ++ s

                lkUp = "(" ++ getTable tableMap t ++ " " ++ ssv i ++ ")"

                cond
                 | hasSign i = "(or " ++ le0 ++ " " ++ gtl ++ ") "
                 | True      = gtl ++ " "

                (less, leq) = case aKnd of
                                KBool         -> error "SBV.SMT.SMTLib2.cvtExp: unexpected boolean valued index"
                                KBounded{}    -> if hasSign i then ("bvslt", "bvsle") else ("bvult", "bvule")
                                KUnbounded    -> ("<", "<=")
                                KReal         -> ("<", "<=")
                                KFloat        -> ("fp.lt", "fp.leq")
                                KDouble       -> ("fp.lt", "fp.geq")
                                KChar         -> error "SBV.SMT.SMTLib2.cvtExp: unexpected string valued index"
                                KString       -> error "SBV.SMT.SMTLib2.cvtExp: unexpected string valued index"
                                KList k       -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected sequence valued index: " ++ show k
                                KSet  k       -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected set valued index: " ++ show k
                                KTuple k      -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected tuple valued index: " ++ show k
                                KMaybe k      -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected maybe valued index: " ++ show k
                                KEither k1 k2 -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected sum valued index: " ++ show (k1, k2)
                                KUserSort s _ -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected uninterpreted valued index: " ++ s

                mkCnst = cvtCV rm . mkConstCV (kindOf i)
                le0  = "(" ++ less ++ " " ++ ssv i ++ " " ++ mkCnst 0 ++ ")"
                gtl  = "(" ++ leq  ++ " " ++ mkCnst l ++ " " ++ ssv i ++ ")"

        sh (SBVApp (KindCast f t) [a]) = handleKindCast f t (ssv a)

        sh (SBVApp (ArrEq i j) [])  = "(= array_" ++ show i ++ " array_" ++ show j ++")"
        sh (SBVApp (ArrRead i) [a]) = "(select array_" ++ show i ++ " " ++ ssv a ++ ")"

        sh (SBVApp (Uninterpreted nm) [])   = nm
        sh (SBVApp (Uninterpreted nm) args) = "(" ++ nm ++ " " ++ unwords (map ssv args) ++ ")"

        sh (SBVApp (Extract i j) [a]) | ensureBV = "((_ extract " ++ show i ++ " " ++ show j ++ ") " ++ ssv a ++ ")"

        sh (SBVApp (Rol i) [a])
           | bvOp  = rot ssv "rotate_left"  i a
           | True  = bad

        sh (SBVApp (Ror i) [a])
           | bvOp  = rot  ssv "rotate_right" i a
           | True  = bad

        sh (SBVApp Shl [a, i])
           | bvOp   = shft ssv "bvshl"  "bvshl" a i
           | True   = bad

        sh (SBVApp Shr [a, i])
           | bvOp  = shft ssv "bvlshr" "bvashr" a i
           | True  = bad

        sh (SBVApp op args)
          | Just f <- lookup op smtBVOpTable, ensureBVOrBool
          = f (any hasSign args) (map ssv args)
          where -- The first 4 operators below do make sense for Integer's in Haskell, but there's
                -- no obvious counterpart for them in the SMTLib translation.
                -- TODO: provide support for these.
                smtBVOpTable = [ (And,  lift2B "and" "bvand")
                               , (Or,   lift2B "or"  "bvor")
                               , (XOr,  lift2B "xor" "bvxor")
                               , (Not,  lift1B "not" "bvnot")
                               , (Join, lift2 "concat")
                               ]

        sh (SBVApp (Label _) [a]) = cvtSV skolemMap a  -- This won't be reached; but just in case!

        sh (SBVApp (IEEEFP (FP_Cast kFrom kTo m)) args) = handleFPCast kFrom kTo (ssv m) (unwords (map ssv args))
        sh (SBVApp (IEEEFP w                    ) args) = "(" ++ show w ++ " " ++ unwords (map ssv args) ++ ")"

        sh (SBVApp (NonLinear w) args) = "(" ++ show w ++ " " ++ unwords (map ssv args) ++ ")"

        sh (SBVApp (PseudoBoolean pb) args)
          | supportsPB = handlePB pb args'
          | True       = reducePB pb args'
          where args' = map ssv args

        -- NB: Z3 semantics have the predicates reversed: i.e., it returns true if overflow isn't possible. Hence the not.
        sh (SBVApp (OverflowOp op) args) = "(not (" ++ show op ++ " " ++ unwords (map ssv args) ++ "))"

        -- Note the unfortunate reversal in StrInRe..
        sh (SBVApp (StrOp (StrInRe r)) args) = "(str.in.re " ++ unwords (map ssv args) ++ " " ++ show r ++ ")"
        sh (SBVApp (StrOp op)          args) = "(" ++ show op ++ " " ++ unwords (map ssv args) ++ ")"

        sh (SBVApp (SeqOp op) args) = "(" ++ show op ++ " " ++ unwords (map ssv args) ++ ")"

        sh (SBVApp (SetOp SetEqual)      args)   = "(= "      ++ unwords (map ssv args) ++ ")"
        sh (SBVApp (SetOp SetMember)     [e, s]) = "(select " ++ ssv s ++ " " ++ ssv e ++ ")"
        sh (SBVApp (SetOp SetInsert)     [e, s]) = "(store "  ++ ssv s ++ " " ++ ssv e ++ " true)"
        sh (SBVApp (SetOp SetDelete)     [e, s]) = "(store "  ++ ssv s ++ " " ++ ssv e ++ " false)"
        sh (SBVApp (SetOp SetIntersect)  args)   = "(intersection " ++ unwords (map ssv args) ++ ")"
        sh (SBVApp (SetOp SetUnion)      args)   = "(union "        ++ unwords (map ssv args) ++ ")"
        sh (SBVApp (SetOp SetSubset)     args)   = "(subset "       ++ unwords (map ssv args) ++ ")"
        sh (SBVApp (SetOp SetDifference) args)   = "(setminus "     ++ unwords (map ssv args) ++ ")"
        sh (SBVApp (SetOp SetComplement) args)   = "(complement "   ++ unwords (map ssv args) ++ ")"
        sh (SBVApp (SetOp SetHasSize)    args)   = "(set-has-size " ++ unwords (map ssv args) ++ ")"

        sh (SBVApp (TupleConstructor 0)   [])    = "mkSBVTuple0"
        sh (SBVApp (TupleConstructor n)   args)  = "(mkSBVTuple" ++ show n ++ " " ++ unwords (map ssv args) ++ ")"
        sh (SBVApp (TupleAccess      i n) [tup]) = "(proj_" ++ show i ++ "_SBVTuple" ++ show n ++ " " ++ ssv tup ++ ")"

        sh (SBVApp (EitherConstructor k1 k2 False) [arg]) =       dtConstructor "left_SBVEither"  [arg] (KEither k1 k2)
        sh (SBVApp (EitherConstructor k1 k2 True ) [arg]) =       dtConstructor "right_SBVEither" [arg] (KEither k1 k2)
        sh (SBVApp (EitherIs          k1 k2 False) [arg]) = '(' : dtAccessor    "left_SBVEither"  [k1]  (KEither k1 k2) ++ " " ++ ssv arg ++ ")"
        sh (SBVApp (EitherIs          k1 k2 True ) [arg]) = '(' : dtAccessor    "right_SBVEither" [k2]  (KEither k1 k2) ++ " " ++ ssv arg ++ ")"
        sh (SBVApp (EitherAccess            False) [arg]) = "(get_left_SBVEither "  ++ ssv arg ++ ")"
        sh (SBVApp (EitherAccess            True ) [arg]) = "(get_right_SBVEither " ++ ssv arg ++ ")"

        sh (SBVApp (MaybeConstructor k False) [])    =       dtConstructor "nothing_SBVMaybe" []    (KMaybe k)
        sh (SBVApp (MaybeConstructor k True)  [arg]) =       dtConstructor "just_SBVMaybe"    [arg] (KMaybe k)
        sh (SBVApp (MaybeIs          k False) [arg]) = '(' : dtAccessor    "nothing_SBVMaybe" []    (KMaybe k) ++ " " ++ ssv arg ++ ")"
        sh (SBVApp (MaybeIs          k True ) [arg]) = '(' : dtAccessor    "just_SBVMaybe"    [k]   (KMaybe k) ++ " " ++ ssv arg ++ ")"
        sh (SBVApp MaybeAccess                [arg]) = "(get_just_SBVMaybe " ++ ssv arg ++ ")"

        sh inp@(SBVApp op args)
          | intOp, Just f <- lookup op smtOpIntTable
          = f True (map ssv args)
          | boolOp, Just f <- lookup op boolComps
          = f (map ssv args)
          | bvOp, Just f <- lookup op smtOpBVTable
          = f (any hasSign args) (map ssv args)
          | realOp, Just f <- lookup op smtOpRealTable
          = f (any hasSign args) (map ssv args)
          | floatOp || doubleOp, Just f <- lookup op smtOpFloatDoubleTable
          = f (any hasSign args) (map ssv args)
          | charOp, Just f <- lookup op smtCharTable
          = f False (map ssv args)
          | stringOp, Just f <- lookup op smtStringTable
          = f (map ssv args)
          | listOp, Just f <- lookup op smtListTable
          = f (map ssv args)
          | Just f <- lookup op uninterpretedTable
          = f (map ssv args)
          | True
          = if not (null args) && isUserSort (head args)
            then error $ unlines [ ""
                                 , "*** Cannot translate operator        : " ++ show op
                                 , "*** When applied to arguments of kind: " ++ intercalate ", " (nub (map (show . kindOf) args))
                                 , "*** Found as part of the expression  : " ++ show inp
                                 , "***"
                                 , "*** Note that uninterpreted kinds only support equality."
                                 , "*** If you believe this is in error, please report!"
                                 ]
            else error $ "SBV.SMT.SMTLib2.cvtExp.sh: impossible happened; can't translate: " ++ show inp
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

                -- equality and comparisons are the only thing that works on uninterpreted sorts and pretty much everything else
                uninterpretedTable = [ (Equal,       lift2S "="        "="        True)
                                     , (NotEqual,    liftNS "distinct" "distinct" True)
                                     , (LessThan,    unintComp "<")
                                     , (GreaterThan, unintComp ">")
                                     , (LessEq,      unintComp "<=")
                                     , (GreaterEq,   unintComp ">=")
                                     ]

                -- For chars, the underlying type is currently SWord8, so we go with the regular bit-vector operations
                -- TODO: This will change when we move to unicode!
                smtCharTable = [ (Equal,         eqBV)
                               , (NotEqual,      neqBV)
                               , (LessThan,      lift2S  "bvult" (error "smtChar.<: did-not expect signed char here!"))
                               , (GreaterThan,   lift2S  "bvugt" (error "smtChar.>: did-not expect signed char here!"))
                               , (LessEq,        lift2S  "bvule" (error "smtChar.<=: did-not expect signed char here!"))
                               , (GreaterEq,     lift2S  "bvuge" (error "smtChar.>=: did-not expect signed char here!"))
                               ]

                -- For strings, equality and comparisons are the only operators
                -- TODO: The string comparison operators will most likely change with the new theory!
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

-----------------------------------------------------------------------------------------------
-- Casts supported by SMTLib. (From: <http://smtlib.cs.uiowa.edu/theories-FloatingPoint.shtml>)
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
handleFPCast kFrom kTo rm input
  | kFrom == kTo
  = input
  | True
  = "(" ++ cast kFrom kTo input ++ ")"
  where addRM a s = s ++ " " ++ rm ++ " " ++ a

        -- To go and back from Ints, we detour through reals
        cast KUnbounded         KFloat             a = "(_ to_fp 8 24) "  ++ rm ++ " (to_real " ++ a ++ ")"
        cast KUnbounded         KDouble            a = "(_ to_fp 11 53) " ++ rm ++ " (to_real " ++ a ++ ")"
        cast KFloat             KUnbounded         a = "to_int (fp.to_real " ++ a ++ ")"
        cast KDouble            KUnbounded         a = "to_int (fp.to_real " ++ a ++ ")"

        -- To float/double
        cast (KBounded False _) KFloat             a = addRM a "(_ to_fp_unsigned 8 24)"
        cast (KBounded False _) KDouble            a = addRM a "(_ to_fp_unsigned 11 53)"
        cast (KBounded True  _) KFloat             a = addRM a "(_ to_fp 8 24)"
        cast (KBounded True  _) KDouble            a = addRM a "(_ to_fp 11 53)"
        cast KReal              KFloat             a = addRM a "(_ to_fp 8 24)"
        cast KReal              KDouble            a = addRM a "(_ to_fp 11 53)"

        -- Between floats
        cast KFloat             KFloat             a = addRM a "(_ to_fp 8 24)"
        cast KFloat             KDouble            a = addRM a "(_ to_fp 11 53)"
        cast KDouble            KFloat             a = addRM a "(_ to_fp 8 24)"
        cast KDouble            KDouble            a = addRM a "(_ to_fp 11 53)"

        -- From float/double
        cast KFloat             (KBounded False m) a = addRM a $ "(_ fp.to_ubv " ++ show m ++ ")"
        cast KDouble            (KBounded False m) a = addRM a $ "(_ fp.to_ubv " ++ show m ++ ")"
        cast KFloat             (KBounded True  m) a = addRM a $ "(_ fp.to_sbv " ++ show m ++ ")"
        cast KDouble            (KBounded True  m) a = addRM a $ "(_ fp.to_sbv " ++ show m ++ ")"

        cast KFloat             KReal              a = "fp.to_real" ++ " " ++ a
        cast KDouble            KReal              a = "fp.to_real" ++ " " ++ a

        -- Nothing else should come up:
        cast f                  d                  _ = error $ "SBV.SMTLib2: Unexpected FPCast from: " ++ show f ++ " to " ++ show d

rot :: (SV -> String) -> String -> Int -> SV -> String
rot ssv o c x = "((_ " ++ o ++ " " ++ show c ++ ") " ++ ssv x ++ ")"

shft :: (SV -> String) -> String -> String -> SV -> SV -> String
shft ssv oW oS x c = "(" ++ o ++ " " ++ ssv x ++ " " ++ ssv c ++ ")"
   where o = if hasSign x then oS else oW

-- Various casts
handleKindCast :: Kind -> Kind -> String -> String
handleKindCast kFrom kTo a
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

        -- NB. The following works regardless n < 0 or not, because the first thing we
        -- do is to compute "reduced" to bring it down to the correct range. It also works
        -- regardless were mapping to signed or unsigned bit-vector; because the representation
        -- is the same.
        --
        -- NB2. (TODO) There is an SMTLib equivalent of this function, called int2bv. However, it
        -- used to be uninterpreted for a long time by Z3; though I think that got fixed. We
        -- might want to simply use that if it's reliably available across the board in solvers.
        i2b n = "((_ int2bv " ++ show n ++ ") " ++ a ++ ")"

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
