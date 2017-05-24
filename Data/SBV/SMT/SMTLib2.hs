----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.SMT.SMTLib2
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Conversion of symbolic programs to SMTLib format, Using v2 of the standard
-----------------------------------------------------------------------------
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}

module Data.SBV.SMT.SMTLib2(cvt, addNonEqConstraints) where

import Data.Bits     (bit)
import Data.Function (on)
import Data.Ord      (comparing)
import Data.List     (intercalate, partition, groupBy, sortBy)
import Data.Maybe    (mapMaybe)

import qualified Data.Foldable as F (toList)
import qualified Data.Map      as M
import qualified Data.IntMap   as IM
import qualified Data.Set      as Set

import Data.SBV.Core.Data

import Data.SBV.Utils.PrettyNum (smtRoundingMode, cwToSMTLib)

-- | Add constraints to generate /new/ models. This function is used to query the SMT-solver, while
-- disallowing a previous model.
addNonEqConstraints :: RoundingMode -> [(Quantifier, NamedSymVar)] -> [[(String, CW)]] -> Maybe [String]
addNonEqConstraints rm qinps allNonEqConstraints
  | null allNonEqConstraints
  = Just []
  | null refutedModel
  = Nothing
  | True
  = Just $ "; --- refuted-models ---" : refutedModel
 where refutedModel = concatMap (nonEqs rm . map intName) nonEqConstraints
       aliasTable   = map (\(_, (x, y)) -> (y, x)) qinps
       intName (s, c)
          | Just sw <- s `lookup` aliasTable = (show sw, c)
          | True                             = (s, c)
       -- with existentials, we only add top-level existentials to the refuted-models list
       nonEqConstraints = filter (not . null) $ map (filter (\(s, _) -> s `elem` topUnivs)) allNonEqConstraints
       topUnivs = [s | (_, (_, s)) <- takeWhile (\p -> fst p == EX) qinps]

nonEqs :: RoundingMode -> [(String, CW)] -> [String]
nonEqs rm scs = format $ interp ps ++ disallow (map eqClass uninterpClasses)
  where isFree (KUserSort _ (Left _)) = True
        isFree _                      = False
        (ups, ps) = partition (isFree . kindOf . snd) scs
        format []     =  []
        format [m]    =  ["(assert " ++ m ++ ")"]
        format (m:ms) =  ["(assert (or " ++ m]
                      ++ map ("            " ++) ms
                      ++ ["        ))"]
        -- Regular (or interpreted) sorts simply get a constraint that we disallow the current assignment
        interp = map $ nonEq rm
        -- Determine the equivalence classes of uninterpreted sorts:
        uninterpClasses = filter (\l -> length l > 1) -- Only need this class if it has at least two members
                        . map (map fst)               -- throw away sorts, we only need the names
                        . groupBy ((==) `on` snd)     -- make sure they belong to the same sort and have the same value
                        . sortBy (comparing snd)      -- sort them according to their sorts first
                        $ ups                         -- take the uninterpreted sorts
        -- Uninterpreted sorts get a constraint that says the equivalence classes as determined by the solver are disallowed:
        eqClass :: [String] -> String
        eqClass [] = error "SBV.allSat.nonEqs: Impossible happened, disallow received an empty list"
        eqClass cs = "(= " ++ unwords cs ++ ")"
        -- Now, take the conjunction of equivalence classes and assert it's negation:
        disallow = map $ \ec -> "(not " ++ ec ++ ")"

nonEq :: RoundingMode -> (String, CW) -> String
nonEq rm (s, c) = "(not (= " ++ s ++ " " ++ cvtCW rm c ++ "))"

tbd :: String -> a
tbd e = error $ "SBV.SMTLib2: Not-yet-supported: " ++ e

-- | Translate a problem into an SMTLib2 script
cvt :: Set.Set Kind                 -- ^ kinds used
    -> Bool                         -- ^ is this a sat problem?
    -> [String]                     -- ^ extra comments to place on top
    -> [(Quantifier, NamedSymVar)]  -- ^ inputs
    -> [Either SW (SW, [SW])]       -- ^ skolemized version inputs
    -> [(SW, CW)]                   -- ^ constants
    -> [((Int, Kind, Kind), [SW])]  -- ^ auto-generated tables
    -> [(Int, ArrayInfo)]           -- ^ user specified arrays
    -> [(String, SBVType)]          -- ^ uninterpreted functions/constants
    -> [(String, [String])]         -- ^ user given axioms
    -> SBVPgm                       -- ^ assignments
    -> [(Maybe String, SW)]         -- ^ extra constraints
    -> SW                           -- ^ output variable
    -> SMTConfig                    -- ^ configuration
    -> CaseCond                     -- ^ case analysis data
    -> [String]
cvt kindInfo isSat comments inputs skolemInps consts tbls arrs uis axs (SBVPgm asgnsSeq) cstrs out config caseCond = pgm
  where hasInteger     = KUnbounded `Set.member` kindInfo
        hasReal        = KReal      `Set.member` kindInfo
        hasFloat       = KFloat     `Set.member` kindInfo
        hasDouble      = KDouble    `Set.member` kindInfo
        hasBVs         = not $ null [() | KBounded{} <- Set.toList kindInfo]
        usorts         = [(s, dt) | KUserSort s dt <- Set.toList kindInfo]
        hasNonBVArrays = (not . null) [() | (_, (_, (k1, k2), _)) <- arrs, not (isBounded k1 && isBounded k2)]
        rm             = roundingMode config
        solverCaps     = capabilities (solver config)

        -- Determining the logic is surprisingly tricky!
        logic
           | Just l <- useLogic config
           = ["(set-logic " ++ show l ++ ") ; NB. User specified."]
           | hasDouble || hasFloat    -- NB. We don't check for quantifiers here, we probably should..
           = if hasBVs
             then ["(set-logic QF_FPBV)"]
             else ["(set-logic QF_FP)"]
           | hasInteger || hasReal || not (null usorts) || hasNonBVArrays
           = let why | hasInteger        = "has unbounded values"
                     | hasReal           = "has algebraic reals"
                     | not (null usorts) = "has user-defined sorts"
                     | hasNonBVArrays    = "has non-bitvector arrays"
                     | True              = "cannot determine the SMTLib-logic to use"
             in case mbDefaultLogic solverCaps hasReal of
                  Nothing -> ["; " ++ why ++ ", no logic specified."]
                  Just l  -> ["(set-logic " ++ l ++ "); " ++ why ++ ", using solver-default logic."]
           | True
           = ["(set-logic " ++ qs ++ as ++ ufs ++ "BV)"]
          where qs  | null foralls && null axs = "QF_"  -- axioms are likely to contain quantifiers
                    | True                     = ""
                as  | null arrs                = ""
                    | True                     = "A"
                ufs | null uis && null tbls    = ""     -- we represent tables as UFs
                    | True                     = "UF"

        getModels
          | supportsProduceModels solverCaps = ["(set-option :produce-models true)"]
          | True                             = []

        unsatCore
          | not (getUnsatCore config)     = []
          | supportsUnsatCores solverCaps = ["(set-option :produce-unsat-cores true)"]
          | True                          = error $ "SBV: unsat cores are requested, but the backend solver " ++ show (solver config) ++ " doesn't support them!"

        pgm  =  ["; Automatically generated by SBV. Do not edit."]
             ++ map ("; " ++) comments
             ++ getModels
             ++ unsatCore
             ++ logic
             ++ [ "; --- uninterpreted sorts ---" ]
             ++ concatMap declSort usorts
             ++ [ "; --- literal constants ---" ]
             ++ concatMap declConst consts
             ++ [ "; --- skolem constants ---" ]
             ++ [ "(declare-fun " ++ show s ++ " " ++ swFunType ss s ++ ")" ++ userName s | Right (s, ss) <- skolemInps]
             ++ [ "; --- constant tables ---" ]
             ++ concatMap constTable constTables
             ++ [ "; --- skolemized tables ---" ]
             ++ map (skolemTable (unwords (map swType foralls))) skolemTables
             ++ [ "; --- arrays ---" ]
             ++ concat arrayConstants
             ++ [ "; --- uninterpreted constants ---" ]
             ++ concatMap declUI uis
             ++ [ "; --- user given axioms ---" ]
             ++ map declAx axs

             ++ [ "; --- formula ---" ]
             ++ ["(assert (forall (" ++ intercalate "\n                 "
                                        ["(" ++ show s ++ " " ++ swType s ++ ")" | s <- foralls] ++ ")"
                | not (null foralls)
                ]

             ++ concatMap mkAssign asgns

             ++ delayedAsserts delayedEqualities

             ++ finalAssert

        noOfCloseParens
          | null foralls = 0
          | True         = length asgns + 2 + (if null delayedEqualities then 0 else 1)

        foralls    = [s | Left s <- skolemInps]
        forallArgs = concatMap ((" " ++) . show) foralls

        (constTables, skolemTables) = ([(t, d) | (t, Left d) <- allTables], [(t, d) | (t, Right d) <- allTables])
        allTables = [(t, genTableData rm skolemMap (not (null foralls), forallArgs) (map fst consts) t) | t <- tbls]
        (arrayConstants, allArrayDelayeds) = unzip $ map (declArray (not (null foralls)) (map fst consts) skolemMap) arrs
        delayedEqualities = concatMap snd skolemTables ++ concat allArrayDelayeds

        delayedAsserts []              = []
        delayedAsserts ds@(deH : deTs)
          | null foralls = map (\s -> "(assert " ++ s ++ ")") ds
          | True         = map letShift (("(and " ++ deH) : map (align 5) deTs)

        letShift = align 12

        finalAssert
          | null foralls
          = map (\a -> "(assert " ++ named a ++ ")") assertions
          | not (null namedAsserts)
          = error $ intercalate "\n" [ "SBV: Named constraints and quantifiers cannot be mixed!"
                                     , "   Quantified variables: " ++ unwords (map show foralls)
                                     , "   Named constraints   : " ++ intercalate ", " (map show namedAsserts)
                                     ]
          | True
          = [impAlign (letShift combined) ++ replicate noOfCloseParens ')']
          where namedAsserts = [n | (Just n, _) <- assertions]

                combined = case map snd assertions of
                             [x] -> x
                             xs  -> "(and " ++ unwords xs ++ ")"

        impAlign s
          | null delayedEqualities = s
          | True                   = "     " ++ s

        align n s = replicate n ' ' ++ s

        -- We have:
        --    - cstrs   : Explicitly given constraints (via calls to constrain)
        --    - p1..pn  : The path conditions in a case-split that led us here. This is given in a case-split.
        --    - c1..cm  : All the other case-split constraints for the coverage case. This is in a case-coverage.
        -- if sat:
        --     -- we assert (cstrs /\ (p1 /\ p2 /\ ... /\ pn) /\ ~(c1 \/ c2 \/ .. \/ cm) /\ out)
        --            i.e., cstrs /\ p1 /\ p2 /\ ... /\ pn /\ ~c1 /\ ~c2 /\ ~c3 .. /\ ~cm /\ out
        -- if prove:
        --     -- we assert ~((cstrs /\  (p1 /\ p2 /\ .. /\ pn) /\ ~(c1 \/ c2 \/ .. \/ cm)) => out)
        --            i.e., cstrs /\ p1 /\ p2 /\ .. /\ pn /\ ~c1 /\ ~c2 /\ ~c3 .. /\ ~cm /\ ~out
        -- That is, we always assert all path constraints and path conditions AND
        --     -- negation of the output in a prove
        --     -- output itself in a sat
        assertions
           | null finals = [(Nothing, cvtSW skolemMap trueSW)]
           | True        = finals

           where finals  = cstrs' ++ maybe [] (\r -> [(Nothing, r)]) mbO

                 cstrs' =  [(mbNm, c') | (mbNm, c) <- cstrs, Just c' <- [pos c]]
                        ++ condAsserts

                 condAsserts = map (Nothing,) $ case caseCond of
                                                    NoCase         -> []
                                                    CasePath ss    -> mapMaybe pos ss
                                                    CaseVac  ss _  -> mapMaybe pos ss
                                                    CaseCov  ss qq -> mapMaybe pos ss ++ mapMaybe neg qq
                                                    CstrVac        -> []
                                                    Opt gs         -> map mkGoal gs

                 mbO | CstrVac     <- caseCond = pos trueSW -- always a SAT call!
                     | CaseVac _ s <- caseCond = pos s      -- always a SAT call!
                     | isSat                   = pos out
                     | True                    = neg out

                 neg s
                  | s == trueSW  = Just $ cvtSW skolemMap falseSW
                  | s == falseSW = Nothing
                  | True         = Just $ "(not " ++ cvtSW skolemMap s ++ ")"

                 pos s
                  | s == trueSW  = Nothing
                  | s == falseSW = Just $ cvtSW skolemMap falseSW
                  | True         = Just $ cvtSW skolemMap s

                 eq (orig, track) = "(= " ++ cvtSW skolemMap track ++ " " ++ cvtSW skolemMap orig ++ ")"
                 mkGoal (Minimize   _ ab)   = eq ab
                 mkGoal (Maximize   _ ab)   = eq ab
                 mkGoal (AssertSoft _ ab _) = eq ab

        skolemMap = M.fromList [(s, ss) | Right (s, ss) <- skolemInps, not (null ss)]
        tableMap  = IM.fromList $ map mkConstTable constTables ++ map mkSkTable skolemTables
          where mkConstTable (((t, _, _), _), _) = (t, "table" ++ show t)
                mkSkTable    (((t, _, _), _), _) = (t, "table" ++ show t ++ forallArgs)
        asgns = F.toList asgnsSeq

        mkAssign a
          | null foralls = mkDef a
          | True         = [letShift (mkLet a)]

        mkDef (s, SBVApp (Label m) [e]) = emit (s, cvtSW                skolemMap          e) (Just m)
        mkDef (s, e)                    = emit (s, cvtExp solverCaps rm skolemMap tableMap e) Nothing

        mkLet (s, SBVApp (Label m) [e]) = "(let ((" ++ show s ++ " " ++ cvtSW                skolemMap          e ++ ")) ; " ++ m
        mkLet (s, e)                    = "(let ((" ++ show s ++ " " ++ cvtExp solverCaps rm skolemMap tableMap e ++ "))"

        -- does the solver allow define-fun; or do we need declare-fun/assert combo?
        useDefFun = supportsDefineFun solverCaps

        declConst (s, c) = emit (s, cvtCW rm c) Nothing

        emit (s, def) mbComment
          | useDefFun = ["(define-fun "   ++ varT ++ " " ++ def ++ ")" ++ cmnt]
          | True      = [ "(declare-fun " ++ varT ++ ")" ++ cmnt
                        , "(assert (= "   ++ show s ++ " " ++ def ++ "))"
                        ]
          where varT = show s ++ " " ++ swFunType [] s
                cmnt = maybe "" (" ; " ++) mbComment

        userName s = case s `lookup` map snd inputs of
                        Just u  | show s /= u -> " ; tracks user variable " ++ show u
                        _ -> ""
        -- following sorts are built-in; do not translate them:
        builtInSort = (`elem` ["RoundingMode"])
        declSort (s, _)
          | builtInSort s           = []
        declSort (s, Left  r ) = ["(declare-sort " ++ s ++ " 0)  ; N.B. Uninterpreted: " ++ r]
        declSort (s, Right fs) = [ "(declare-datatypes () ((" ++ s ++ " " ++ unwords (map (\c -> "(" ++ c ++ ")") fs) ++ ")))"
                                 , "(define-fun " ++ s ++ "_constrIndex ((x " ++ s ++ ")) Int"
                                 ] ++ ["   " ++ body fs (0::Int)] ++ [")"]
                where body []     _ = ""
                      body [_]    i = show i
                      body (c:cs) i = "(ite (= x " ++ c ++ ") " ++ show i ++ " " ++ body cs (i+1) ++ ")"

declUI :: (String, SBVType) -> [String]
declUI (i, t) = ["(declare-fun " ++ i ++ " " ++ cvtType t ++ ")"]

-- NB. We perform no check to as to whether the axiom is meaningful in any way.
declAx :: (String, [String]) -> String
declAx (nm, ls) = (";; -- user given axiom: " ++ nm ++ "\n") ++ intercalate "\n" ls

constTable :: (((Int, Kind, Kind), [SW]), [String]) -> [String]
constTable (((i, ak, rk), _elts), is) = decl : map wrap is
  where t       = "table" ++ show i
        decl    = "(declare-fun " ++ t ++ " (" ++ smtType ak ++ ") " ++ smtType rk ++ ")"
        wrap  s = "(assert " ++ s ++ ")"

skolemTable :: String -> (((Int, Kind, Kind), [SW]), [String]) -> String
skolemTable qsIn (((i, ak, rk), _elts), _) = decl
  where qs   = if null qsIn then "" else qsIn ++ " "
        t    = "table" ++ show i
        decl = "(declare-fun " ++ t ++ " (" ++ qs ++ smtType ak ++ ") " ++ smtType rk ++ ")"

-- Left if all constants, Right if otherwise
genTableData :: RoundingMode -> SkolemMap -> (Bool, String) -> [SW] -> ((Int, Kind, Kind), [SW]) -> Either [String] [String]
genTableData rm skolemMap (_quantified, args) consts ((i, aknd, _), elts)
  | null post = Left  (map (topLevel . snd) pre)
  | True      = Right (map (nested   . snd) (pre ++ post))
  where ssw = cvtSW skolemMap
        (pre, post) = partition fst (zipWith mkElt elts [(0::Int)..])
        t           = "table" ++ show i
        mkElt x k   = (isReady, (idx, ssw x))
          where idx = cvtCW rm (mkConstCW aknd k)
                isReady = x `Set.member` constsSet
        topLevel (idx, v) = "(= (" ++ t ++ " " ++ idx ++ ") " ++ v ++ ")"
        nested   (idx, v) = "(= (" ++ t ++ args ++ " " ++ idx ++ ") " ++ v ++ ")"
        constsSet = Set.fromList consts

-- TODO: We currently do not support non-constant arrays when quantifiers are present, as
-- we might have to skolemize those. Implement this properly.
-- The difficulty is with the ArrayReset/Mutate/Merge: We have to postpone an init if
-- the components are themselves postponed, so this cannot be implemented as a simple map.
declArray :: Bool -> [SW] -> SkolemMap -> (Int, ArrayInfo) -> ([String], [String])
declArray quantified consts skolemMap (i, (_, (aKnd, bKnd), ctx)) = (adecl : map wrap pre, map snd post)
  where topLevel = not quantified || case ctx of
                                       ArrayFree Nothing -> True
                                       ArrayFree (Just sw) -> sw `elem` consts
                                       ArrayReset _ sw     -> sw `elem` consts
                                       ArrayMutate _ a b   -> all (`elem` consts) [a, b]
                                       ArrayMerge c _ _    -> c `elem` consts
        (pre, post) = partition fst ctxInfo
        nm = "array_" ++ show i
        ssw sw
         | topLevel || sw `elem` consts
         = cvtSW skolemMap sw
         | True
         = tbd "Non-constant array initializer in a quantified context"
        adecl = "(declare-fun " ++ nm ++ " () (Array " ++ smtType aKnd ++ " " ++ smtType bKnd ++ "))"
        ctxInfo = case ctx of
                    ArrayFree Nothing   -> []
                    ArrayFree (Just sw) -> declA sw
                    ArrayReset _ sw     -> declA sw
                    ArrayMutate j a b -> [(all (`elem` consts) [a, b], "(= " ++ nm ++ " (store array_" ++ show j ++ " " ++ ssw a ++ " " ++ ssw b ++ "))")]
                    ArrayMerge  t j k -> [(t `elem` consts,            "(= " ++ nm ++ " (ite " ++ ssw t ++ " array_" ++ show j ++ " array_" ++ show k ++ "))")]
        declA sw = let iv = nm ++ "_freeInitializer"
                   in [ (True,             "(declare-fun " ++ iv ++ " () " ++ smtType aKnd ++ ")")
                      , (sw `elem` consts, "(= (select " ++ nm ++ " " ++ iv ++ ") " ++ ssw sw ++ ")")
                      ]
        wrap (False, s) = s
        wrap (True, s)  = "(assert " ++ s ++ ")"

swType :: SW -> String
swType s = smtType (kindOf s)

swFunType :: [SW] -> SW -> String
swFunType ss s = "(" ++ unwords (map swType ss) ++ ") " ++ swType s

smtType :: Kind -> String
smtType KBool           = "Bool"
smtType (KBounded _ sz) = "(_ BitVec " ++ show sz ++ ")"
smtType KUnbounded      = "Int"
smtType KReal           = "Real"
smtType KFloat          = "(_ FloatingPoint  8 24)"
smtType KDouble         = "(_ FloatingPoint 11 53)"
smtType (KUserSort s _) = s

cvtType :: SBVType -> String
cvtType (SBVType []) = error "SBV.SMT.SMTLib2.cvtType: internal: received an empty type!"
cvtType (SBVType xs) = "(" ++ unwords (map smtType body) ++ ") " ++ smtType ret
  where (body, ret) = (init xs, last xs)

type SkolemMap = M.Map  SW [SW]
type TableMap  = IM.IntMap String

cvtSW :: SkolemMap -> SW -> String
cvtSW skolemMap s
  | Just ss <- s `M.lookup` skolemMap
  = "(" ++ show s ++ concatMap ((" " ++) . show) ss ++ ")"
  | True
  = show s

cvtCW :: RoundingMode -> CW -> String
cvtCW = cwToSMTLib

getTable :: TableMap -> Int -> String
getTable m i
  | Just tn <- i `IM.lookup` m = tn
  | True                       = error $ "SBV.SMTLib2: Cannot locate table " ++ show i

cvtExp :: SolverCapabilities -> RoundingMode -> SkolemMap -> TableMap -> SBVExpr -> String
cvtExp caps rm skolemMap tableMap expr@(SBVApp _ arguments) = sh expr
  where ssw = cvtSW skolemMap

        supportsPB = supportsPseudoBooleans caps

        bvOp     = all isBounded arguments
        intOp    = any isInteger arguments
        realOp   = any isReal    arguments
        doubleOp = any isDouble  arguments
        floatOp  = any isFloat   arguments
        boolOp   = all isBoolean arguments

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
                        z   = cvtCW rm (mkConstCW (kindOf (head arguments)) (0::Integer))

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
          | KUserSort s (Right _) <- kindOf (head arguments)
          = let idx v = "(" ++ s ++ "_constrIndex " ++ " " ++ v ++ ")" in "(" ++ o ++ " " ++ idx a ++ " " ++ idx b ++ ")"
        unintComp o sbvs = error $ "SBV.SMT.SMTLib2.sh.unintComp: Unexpected arguments: "   ++ show (o, sbvs)

        lift1  o _ [x]    = "(" ++ o ++ " " ++ x ++ ")"
        lift1  o _ sbvs   = error $ "SBV.SMT.SMTLib2.sh.lift1: Unexpected arguments: "   ++ show (o, sbvs)

        sh (SBVApp Ite [a, b, c]) = "(ite " ++ ssw a ++ " " ++ ssw b ++ " " ++ ssw c ++ ")"

        sh (SBVApp (LkUp (t, aKnd, _, l) i e) [])
          | needsCheck = "(ite " ++ cond ++ ssw e ++ " " ++ lkUp ++ ")"
          | True       = lkUp
          where needsCheck = case aKnd of
                              KBool         -> (2::Integer) > fromIntegral l
                              KBounded _ n  -> (2::Integer)^n > fromIntegral l
                              KUnbounded    -> True
                              KReal         -> error "SBV.SMT.SMTLib2.cvtExp: unexpected real valued index"
                              KFloat        -> error "SBV.SMT.SMTLib2.cvtExp: unexpected float valued index"
                              KDouble       -> error "SBV.SMT.SMTLib2.cvtExp: unexpected double valued index"
                              KUserSort s _ -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected uninterpreted valued index: " ++ s
                lkUp = "(" ++ getTable tableMap t ++ " " ++ ssw i ++ ")"
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
                                KUserSort s _ -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected uninterpreted valued index: " ++ s
                mkCnst = cvtCW rm . mkConstCW (kindOf i)
                le0  = "(" ++ less ++ " " ++ ssw i ++ " " ++ mkCnst 0 ++ ")"
                gtl  = "(" ++ leq  ++ " " ++ mkCnst l ++ " " ++ ssw i ++ ")"

        sh (SBVApp (KindCast f t) [a]) = handleKindCast f t (ssw a)

        sh (SBVApp (ArrEq i j) [])  = "(= array_" ++ show i ++ " array_" ++ show j ++")"
        sh (SBVApp (ArrRead i) [a]) = "(select array_" ++ show i ++ " " ++ ssw a ++ ")"

        sh (SBVApp (Uninterpreted nm) [])   = nm
        sh (SBVApp (Uninterpreted nm) args) = "(" ++ nm ++ " " ++ unwords (map ssw args) ++ ")"

        sh (SBVApp (Extract i j) [a]) | ensureBV = "((_ extract " ++ show i ++ " " ++ show j ++ ") " ++ ssw a ++ ")"

        sh (SBVApp (Rol i) [a])
           | bvOp  = rot  ssw "rotate_left"  i a
           | intOp = sh (SBVApp (Shl i) [a])       -- Haskell treats rotateL as shiftL for unbounded values
           | True  = bad

        sh (SBVApp (Ror i) [a])
           | bvOp  = rot  ssw "rotate_right" i a
           | intOp = sh (SBVApp (Shr i) [a])     -- Haskell treats rotateR as shiftR for unbounded values
           | True  = bad

        sh (SBVApp (Shl i) [a])
           | bvOp   = shft rm ssw "bvshl"  "bvshl"  i a
           | i < 0  = sh (SBVApp (Shr (-i)) [a])  -- flip sign/direction
           | intOp  = "(* " ++ ssw a ++ " " ++ show (bit i :: Integer) ++ ")"  -- Implement shiftL by multiplication by 2^i
           | True   = bad

        sh (SBVApp (Shr i) [a])
           | bvOp  = shft rm ssw "bvlshr" "bvashr" i a
           | i < 0 = sh (SBVApp (Shl (-i)) [a])  -- flip sign/direction
           | intOp = "(div " ++ ssw a ++ " " ++ show (bit i :: Integer) ++ ")"  -- Implement shiftR by division by 2^i
           | True  = bad

        sh (SBVApp op args)
          | Just f <- lookup op smtBVOpTable, ensureBVOrBool
          = f (any hasSign args) (map ssw args)
          where -- The first 4 operators below do make sense for Integer's in Haskell, but there's
                -- no obvious counterpart for them in the SMTLib translation.
                -- TODO: provide support for these.
                smtBVOpTable = [ (And,  lift2B "and" "bvand")
                               , (Or,   lift2B "or"  "bvor")
                               , (XOr,  lift2B "xor" "bvxor")
                               , (Not,  lift1B "not" "bvnot")
                               , (Join, lift2 "concat")
                               ]

        sh (SBVApp (Label m) [a]) = curry named (Just m) $ cvtSW skolemMap a  -- This won't be reached; but just in case!

        sh (SBVApp (IEEEFP (FP_Cast kFrom kTo m)) args) = handleFPCast kFrom kTo (ssw m) (unwords (map ssw args))
        sh (SBVApp (IEEEFP w                    ) args) = "(" ++ show w ++ " " ++ unwords (map ssw args) ++ ")"

        sh (SBVApp (PseudoBoolean pb) args)
          | supportsPB = handlePB pb args'
          | True       = reducePB pb args'
          where args' = map ssw args

        sh inp@(SBVApp op args)
          | intOp, Just f <- lookup op smtOpIntTable
          = f True (map ssw args)
          | boolOp, Just f <- lookup op boolComps
          = f (map ssw args)
          | bvOp, Just f <- lookup op smtOpBVTable
          = f (any hasSign args) (map ssw args)
          | realOp, Just f <- lookup op smtOpRealTable
          = f (any hasSign args) (map ssw args)
          | floatOp || doubleOp, Just f <- lookup op smtOpFloatDoubleTable
          = f (any hasSign args) (map ssw args)
          | Just f <- lookup op uninterpretedTable
          = f (map ssw args)
          | True
          = error $ "SBV.SMT.SMTLib2.cvtExp.sh: impossible happened; can't translate: " ++ show inp
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
                -- equality and comparisons are the only thing that works on uninterpreted sorts
                uninterpretedTable = [ (Equal,       lift2S "="        "="        True)
                                     , (NotEqual,    liftNS "distinct" "distinct" True)
                                     , (LessThan,    unintComp "<")
                                     , (GreaterThan, unintComp ">")
                                     , (LessEq,      unintComp "<=")
                                     , (GreaterEq,   unintComp ">=")
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

rot :: (SW -> String) -> String -> Int -> SW -> String
rot ssw o c x = "((_ " ++ o ++ " " ++ show c ++ ") " ++ ssw x ++ ")"

shft :: RoundingMode -> (SW -> String) -> String -> String -> Int -> SW -> String
shft rm ssw oW oS c x = "(" ++ o ++ " " ++ ssw x ++ " " ++ cvtCW rm c' ++ ")"
   where s  = hasSign x
         c' = mkConstCW (kindOf x) c
         o  = if s then oS else oW

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

-- Add a named annotation
named :: (Maybe String, String) -> String
named (Nothing, x) = x
named (Just nm, x) = "(! " ++ x ++ " :named |" ++ concatMap sanitize nm ++ "|)"
  where sanitize '|'  = "_bar_"
        sanitize '\\' = "_backslash_"
        sanitize c    = [c]
