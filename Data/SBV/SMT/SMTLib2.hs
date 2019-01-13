-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.SMT.SMTLib2
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Conversion of symbolic programs to SMTLib format, Using v2 of the standard
-----------------------------------------------------------------------------

{-# LANGUAGE PatternGuards #-}

module Data.SBV.SMT.SMTLib2(cvt, cvtInc) where

import Data.Bits  (bit)
import Data.List  (intercalate, partition, unzip3, nub, sort)
import Data.Maybe (listToMaybe, fromMaybe)

import qualified Data.Foldable as F (toList)
import qualified Data.Map.Strict      as M
import qualified Data.IntMap.Strict   as IM
import           Data.Set             (Set)
import qualified Data.Set             as Set

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic (QueryContext(..))
import Data.SBV.Core.Kind (smtType)
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
        hasBVs         = hasChar || not (null [() | KBounded{} <- Set.toList kindInfo])   -- Remember, characters map to Word8
        usorts         = [(s, dt) | KUninterpreted s dt <- Set.toList kindInfo]
        tupleArities   = findTupleArities kindInfo
        hasNonBVArrays = (not . null) [() | (_, (_, (k1, k2), _)) <- arrs, not (isBounded k1 && isBounded k2)]
        hasArrayInits  = (not . null) [() | (_, (_, _, ArrayFree (Just _))) <- arrs]
        hasList        = any isList kindInfo
        hasTuples      = not . null $ tupleArities
        rm             = roundingMode cfg
        solverCaps     = capabilities (solver cfg)

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

           -- Otherwise, we try to determine the most suitable logic.
           -- NB. This isn't really fool proof!

           -- we never set QF_S (ALL seems to work better in all cases)

           | hasArrayInits
           = ["(set-logic ALL)"]

           | hasString || hasList
           = ["(set-logic ALL)"]

           | hasDouble || hasFloat
           = if hasInteger || not (null foralls)
             then ["(set-logic ALL)"]
             else if hasBVs
                  then ["(set-logic QF_FPBV)"]
                  else ["(set-logic QF_FP)"]
           | hasInteger || hasReal || not (null usorts) || hasNonBVArrays || hasTuples
           = let why | hasInteger        = "has unbounded values"
                     | hasReal           = "has algebraic reals"
                     | not (null usorts) = "has user-defined sorts"
                     | hasNonBVArrays    = "has non-bitvector arrays"
                     | hasTuples         = "has tuples"
                     | True              = "cannot determine the SMTLib-logic to use"
             in ["(set-logic ALL) ; "  ++ why ++ ", using catch-all."]

           -- If we're in a user query context, we'll pick ALL, otherwise
           -- we'll stick to some bit-vector logic based on what we see in the problem.
           -- This is controversial, but seems to work well in practice.
           | True
           = case ctx of
               QueryExternal -> ["(set-logic ALL) ; external query, using all logics."]
               QueryInternal -> ["(set-logic " ++ qs ++ as ++ ufs ++ "BV)"]
          where qs  | null foralls && null axs = "QF_"  -- axioms are likely to contain quantifiers
                    | True                     = ""
                as  | null arrs                = ""
                    | True                     = "A"
                ufs | null uis && null tbls    = ""     -- we represent tables as UFs
                    | True                     = "UF"

        -- SBV always requires the production of models!
        getModels   = "(set-option :produce-models true)"
                    : concat [flattenConfig | hasList, Just flattenConfig <- [supportsFlattenedSequences solverCaps]]

        -- process all other settings we're given
        userSettings = concatMap opts $ solverSetOptions cfg
           where opts SetLogic{} = []     -- processed already
                 opts o          = [setSMTOption o]

        settings =  userSettings        -- NB. Make sure this comes first!
                 ++ getModels
                 ++ logic

        pgm  =  map ("; " ++) comments
             ++ settings
             ++ [ "; --- uninterpreted sorts ---" ]
             ++ concatMap declSort usorts
             ++ [ "; --- tuples ---" ]
             ++ concatMap declTuple tupleArities
             ++ [ "; --- literal constants ---" ]
             ++ concatMap (declConst cfg) consts
             ++ [ "; --- skolem constants ---" ]
             ++ [ "(declare-fun " ++ show s ++ " " ++ svFunType ss s ++ ")" ++ userName s | Right (s, ss) <- skolemInps]
             ++ [ "; --- optimization tracker variables ---" | not (null trackerVars) ]
             ++ [ "(declare-fun " ++ show s ++ " " ++ svFunType [] s ++ ") ; tracks " ++ nm | (s, nm) <- trackerVars]
             ++ [ "; --- constant tables ---" ]
             ++ concatMap (constTable False) constTables
             ++ [ "; --- skolemized tables ---" ]
             ++ map (skolemTable (unwords (map svType foralls))) skolemTables
             ++ [ "; --- arrays ---" ]
             ++ concat arrayConstants
             ++ [ "; --- uninterpreted constants ---" ]
             ++ concatMap declUI uis
             ++ [ "; --- user given axioms ---" ]
             ++ map declAx axs
             ++ [ "; --- formula ---" ]

             ++ map (declDef cfg skolemMap tableMap) preQuantifierAssigns
             ++ ["(assert (forall (" ++ intercalate "\n                 "
                                        ["(" ++ show s ++ " " ++ svType s ++ ")" | s <- foralls] ++ ")"
                | not (null foralls)
                ]
             ++ map mkAssign postQuantifierAssigns

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
        (arrayConstants, arrayDelayeds, arraySetups) = unzip3 $ map (declArray cfg False (not (null foralls)) consts skolemMap) arrs
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

                 cstrs' =  [(isSoft, attrs, c') | (isSoft, attrs, c) <- cstrs, Just c' <- [pos c]]

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
          | True         = letShift (mkLet a)

        mkLet (s, SBVApp (Label m) [e]) = "(let ((" ++ show s ++ " " ++ cvtSV                skolemMap          e ++ ")) ; " ++ m
        mkLet (s, e)                    = "(let ((" ++ show s ++ " " ++ cvtExp solverCaps rm skolemMap tableMap e ++ "))"

        userName s = case s `lookup` map snd inputs of
                        Just u  | show s /= u -> " ; tracks user variable " ++ show u
                        _ -> ""

-- | Declare new sorts
declSort :: (String, Either String [String]) -> [String]
declSort (s, _)
  | s == "RoundingMode" -- built-in-sort; so don't declare.
  = []
declSort (s, Left  r ) = ["(declare-sort " ++ s ++ " 0)  ; N.B. Uninterpreted: " ++ r]
declSort (s, Right fs) = [ "(declare-datatypes () ((" ++ s ++ " " ++ unwords (map (\c -> "(" ++ c ++ ")") fs) ++ ")))"
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
  | arity == 0 = ["(declare-datatypes () ((SBVTuple0 SBVTuple0)))"]
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

-- | Convert in a query context
cvtInc :: Bool -> SMTLibIncConverter [String]
cvtInc afterAPush inps newKs consts arrs tbls uis (SBVPgm asgnsSeq) cfg =
            -- sorts
               concatMap declSort [(s, dt) | KUninterpreted s dt <- Set.toList newKs]
            -- tuples. NB. Only declare the new sizes, old sizes persist.
            ++ concatMap declTuple (findTupleArities newKs)
            -- constants
            ++ concatMap (declConst cfg) consts
            -- inputs
            ++ map declInp inps
            -- arrays
            ++ concat arrayConstants
            -- uninterpreteds
            ++ concatMap declUI uis
            -- tables
            ++ concatMap (constTable afterAPush) allTables
            -- expressions
            ++ map  (declDef cfg skolemMap tableMap) (F.toList asgnsSeq)
            -- delayed equalities
            ++ concat arrayDelayeds
            -- array setups
            ++ concat arraySetups
  where -- NB. The below setting of skolemMap to empty is OK, since we do
        -- not support queries in the context of skolemized variables
        skolemMap = M.empty

        rm = roundingMode cfg

        declInp (s, _) = "(declare-fun " ++ show s ++ " () " ++ svType s ++ ")"

        (arrayConstants, arrayDelayeds, arraySetups) = unzip3 $ map (declArray cfg afterAPush False consts skolemMap) arrs

        allTables = [(t, either id id (genTableData rm skolemMap (False, []) (map fst consts) t)) | t <- tbls]
        tableMap  = IM.fromList $ map mkTable allTables
          where mkTable (((t, _, _), _), _) = (t, "table" ++ show t)

declDef :: SMTConfig -> SkolemMap -> TableMap -> (SV, SBVExpr) -> String
declDef cfg skolemMap tableMap (s, expr) =
        case expr of
          SBVApp  (Label m) [e] -> defineFun (s, cvtSV          skolemMap          e) (Just m)
          e                     -> defineFun (s, cvtExp caps rm skolemMap tableMap e) Nothing
  where caps = capabilities (solver cfg)
        rm   = roundingMode cfg

defineFun :: (SV, String) -> Maybe String -> String
defineFun (s, def) mbComment = "(define-fun "   ++ varT ++ " " ++ def ++ ")" ++ cmnt
  where varT      = show s ++ " " ++ svFunType [] s
        cmnt      = maybe "" (" ; " ++) mbComment

-- Declare constants. NB. We don't declare true/false; but just inline those as necessary
declConst :: SMTConfig -> (SV, CV) -> [String]
declConst cfg (s, c)
  | s == falseSV || s == trueSV
  = []
  | True
  = [defineFun (s, cvtCV (roundingMode cfg) c) Nothing]

declUI :: (String, SBVType) -> [String]
declUI (i, t) = ["(declare-fun " ++ i ++ " " ++ cvtType t ++ ")"]

-- NB. We perform no check to as to whether the axiom is meaningful in any way.
declAx :: (String, [String]) -> String
declAx (nm, ls) = (";; -- user given axiom: " ++ nm ++ "\n") ++ intercalate "\n" ls

constTable :: Bool -> (((Int, Kind, Kind), [SV]), [String]) -> [String]
constTable afterAPush (((i, ak, rk), _elts), is) = decl : zipWith wrap [(0::Int)..] is ++ setup
  where t       = "table" ++ show i
        decl    = "(declare-fun " ++ t ++ " (" ++ smtType ak ++ ") " ++ smtType rk ++ ")"

        -- Arrange for initializers
        mkInit idx   = "table" ++ show i ++ "_initializer_" ++ show (idx :: Int)
        initializer  = "table" ++ show i ++ "_initializer"
        wrap index s
          | afterAPush = "(define-fun " ++ mkInit index ++ " () Bool " ++ s ++ ")"
          | True       = "(assert " ++ s ++ ")"
        lis          = length is
        setup
          | not afterAPush = []
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
declArray :: SMTConfig -> Bool -> Bool -> [(SV, CV)] -> SkolemMap -> (Int, ArrayInfo) -> ([String], [String], [String])
declArray cfg afterAPush quantified consts skolemMap (i, (_, (aKnd, bKnd), ctx)) = (adecl : zipWith wrap [(0::Int)..] (map snd pre), zipWith wrap [lpre..] (map snd post), setup)
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

        wrap index s
          | afterAPush = "(define-fun " ++ mkInit index ++ " () Bool " ++ s ++ ")"
          | True       = "(assert " ++ s ++ ")"

        lpre          = length pre
        lAll          = lpre + length post

        setup
          | not afterAPush = []
          | lAll == 0      = [ "(define-fun " ++ initializer ++ " () Bool true) ; no initializiation needed"
                             ]
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

        bvOp     = all isBounded arguments
        intOp    = any isInteger arguments
        realOp   = any isReal    arguments
        doubleOp = any isDouble  arguments
        floatOp  = any isFloat   arguments
        boolOp   = all isBoolean arguments
        charOp   = any isChar    arguments
        stringOp = any isString  arguments
        listOp   = any isList    arguments

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
          | doubleOp = liftP sbvs
          | floatOp  = liftP sbvs
          | True     = liftN "distinct" sgn sbvs
          where liftP [_, _] = "(not " ++ equal sgn sbvs ++ ")"
                liftP args   = "(and " ++ unwords (walk args) ++ ")"

                walk []     = []
                walk (e:es) = map (pair e) es ++ walk es

                pair e1 e2  = "(not (fp.eq " ++ e1 ++ " " ++ e2 ++ "))"

        lift2S oU oS sgn = lift2 (if sgn then oS else oU) sgn
        liftNS oU oS sgn = liftN (if sgn then oS else oU) sgn

        lift2Cmp o fo | doubleOp || floatOp = lift2 fo
                      | True                = lift2 o

        unintComp o [a, b]
          | KUninterpreted s (Right _) <- kindOf (head arguments)
          = let idx v = "(" ++ s ++ "_constrIndex " ++ v ++ ")" in "(" ++ o ++ " " ++ idx a ++ " " ++ idx b ++ ")"
        unintComp o sbvs = error $ "SBV.SMT.SMTLib2.sh.unintComp: Unexpected arguments: "   ++ show (o, sbvs)

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

        sh (SBVApp Ite [a, b, c]) = "(ite " ++ ssv a ++ " " ++ ssv b ++ " " ++ ssv c ++ ")"

        sh (SBVApp (LkUp (t, aKnd, _, l) i e) [])
          | needsCheck = "(ite " ++ cond ++ ssv e ++ " " ++ lkUp ++ ")"
          | True       = lkUp
          where needsCheck = case aKnd of
                              KBool              -> (2::Integer) > fromIntegral l
                              KBounded _ n       -> (2::Integer)^n > fromIntegral l
                              KUnbounded         -> True
                              KReal              -> error "SBV.SMT.SMTLib2.cvtExp: unexpected real valued index"
                              KFloat             -> error "SBV.SMT.SMTLib2.cvtExp: unexpected float valued index"
                              KDouble            -> error "SBV.SMT.SMTLib2.cvtExp: unexpected double valued index"
                              KChar              -> error "SBV.SMT.SMTLib2.cvtExp: unexpected char valued index"
                              KString            -> error "SBV.SMT.SMTLib2.cvtExp: unexpected string valued index"
                              KList k            -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected list valued: " ++ show k
                              KTuple k           -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected tuple valued: " ++ show k
                              KUninterpreted s _ -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected uninterpreted valued index: " ++ s

                lkUp = "(" ++ getTable tableMap t ++ " " ++ ssv i ++ ")"

                cond
                 | hasSign i = "(or " ++ le0 ++ " " ++ gtl ++ ") "
                 | True      = gtl ++ " "

                (less, leq) = case aKnd of
                                KBool              -> error "SBV.SMT.SMTLib2.cvtExp: unexpected boolean valued index"
                                KBounded{}         -> if hasSign i then ("bvslt", "bvsle") else ("bvult", "bvule")
                                KUnbounded         -> ("<", "<=")
                                KReal              -> ("<", "<=")
                                KFloat             -> ("fp.lt", "fp.leq")
                                KDouble            -> ("fp.lt", "fp.geq")
                                KChar              -> error "SBV.SMT.SMTLib2.cvtExp: unexpected string valued index"
                                KString            -> error "SBV.SMT.SMTLib2.cvtExp: unexpected string valued index"
                                KList k            -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected sequence valued index: " ++ show k
                                KTuple k           -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected tuple valued index: " ++ show k
                                KUninterpreted s _ -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected uninterpreted valued index: " ++ s

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

        sh (SBVApp (TupleConstructor 0)   [])    = "SBVTuple0"
        sh (SBVApp (TupleConstructor n)   args)  = "(mkSBVTuple" ++ show n ++ " " ++ unwords (map ssv args) ++ ")"
        sh (SBVApp (TupleAccess      i n) [tup]) = "(proj_" ++ show i ++ "_SBVTuple" ++ show n ++ " " ++ ssv tup ++ ")"

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
          = if not (null args) && isUninterpreted (head args)
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

        absRM a s = "ite (fp.isNegative " ++ a ++ ") (" ++ cvt1 ++ ") (" ++ cvt2 ++ ")"
          where cvt1 = "bvneg (" ++ s ++ " " ++ rm ++ " (fp.abs " ++ a ++ "))"
                cvt2 =              s ++ " " ++ rm ++ " "         ++ a

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
        cast KFloat             (KBounded False m) a = absRM a $ "(_ fp.to_ubv " ++ show m ++ ")"
        cast KDouble            (KBounded False m) a = absRM a $ "(_ fp.to_ubv " ++ show m ++ ")"
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

        -- NB. The following works regardless n < 0 or not, because the first thing we
        -- do is to compute "reduced" to bring it down to the correct range. It also works
        -- regardless were mapping to signed or unsigned bit-vector; because the representation
        -- is the same.
        --
        -- NB2. (TODO) There is an SMTLib equivalent of this function, called int2bv. However, it
        -- used to be uninterpreted for a long time by Z3; though I think that got fixed. We
        -- might want to simply use that if it's reliably available across the board in solvers.
        i2b n = "(let (" ++ reduced ++ ") (let (" ++ defs ++ ") " ++ body ++ "))"
          where b i      = show (bit i :: Integer)
                reduced  = "(__a (mod " ++ a ++ " " ++ b n ++ "))"
                mkBit 0  = "(__a0 (ite (= (mod __a 2) 0) #b0 #b1))"
                mkBit i  = "(__a" ++ show i ++ " (ite (= (mod (div __a " ++ b i ++ ") 2) 0) #b0 #b1))"
                defs     = unwords (map mkBit [0 .. n - 1])
                body     = foldr1 (\c r -> "(concat " ++ c ++ " " ++ r ++ ")") ["__a" ++ show i | i <- [n-1, n-2 .. 0]]

        b2i s m
          | s    = "(- " ++ val ++ " " ++ valIf (2^m) sign ++ ")"
          | True = val
          where valIf v b = "(ite (= " ++ b ++ " #b1) " ++ show (v::Integer) ++ " 0)"
                getBit i  = "((_ extract " ++ show i ++ " " ++ show i ++ ") " ++ a ++ ")"
                bitVal i  = valIf (2^i) (getBit i)
                val       = "(+ " ++ unwords (map bitVal [0 .. m-1]) ++ ")"
                sign      = getBit (m-1)

        signExtend i = "((_ sign_extend " ++ show i ++  ") "  ++ a ++ ")"
        zeroExtend i = "((_ zero_extend " ++ show i ++  ") "  ++ a ++ ")"
        extract    i = "((_ extract "     ++ show i ++ " 0) " ++ a ++ ")"

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
