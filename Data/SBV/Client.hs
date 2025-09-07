-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Client
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Cross-cutting toplevel client functions
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DeriveLift          #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PackageImports      #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TupleSections       #-}

#if MIN_VERSION_template_haskell(2,22,1)
-- No need for newer versions of TH
#else
{-# LANGUAGE FlexibleInstances   #-}
#endif

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module Data.SBV.Client
  ( sbvCheckSolverInstallation
  , defaultSolverConfig
  , getAvailableSolvers
  , mkSymbolic
  , getConstructors
  ) where

import Data.Generics

import Control.Monad (filterM)
import Test.QuickCheck (Arbitrary(..), arbitraryBoundedEnum)

import qualified Control.Exception as C

import Data.Maybe (fromMaybe)

import Data.Word
import Data.Int
import Data.Ratio

import qualified "template-haskell" Language.Haskell.TH        as TH
#if MIN_VERSION_template_haskell(2,18,0)
import qualified "template-haskell" Language.Haskell.TH.Syntax as TH
#endif

import Language.Haskell.TH.ExpandSyns as TH

import Data.SBV.Core.Data
import Data.SBV.Core.Model
import Data.SBV.Core.Operations
import Data.SBV.Core.SizedFloats
import Data.SBV.Provers.Prover
import qualified Data.SBV.List as SL


-- | Check whether the given solver is installed and is ready to go. This call does a
-- simple call to the solver to ensure all is well.
sbvCheckSolverInstallation :: SMTConfig -> IO Bool
sbvCheckSolverInstallation cfg = check `C.catch` (\(_ :: C.SomeException) -> return False)
  where check = do ThmResult r <- proveWith cfg $ \x -> sNot (sNot x) .== (x :: SBool)
                   case r of
                     Unsatisfiable{} -> return True
                     _               -> return False

-- | The default configs corresponding to supported SMT solvers
defaultSolverConfig :: Solver -> SMTConfig
defaultSolverConfig ABC       = abc
defaultSolverConfig Boolector = boolector
defaultSolverConfig Bitwuzla  = bitwuzla
defaultSolverConfig CVC4      = cvc4
defaultSolverConfig CVC5      = cvc5
defaultSolverConfig DReal     = dReal
defaultSolverConfig MathSAT   = mathSAT
defaultSolverConfig OpenSMT   = openSMT
defaultSolverConfig Yices     = yices
defaultSolverConfig Z3        = z3

-- | Return the known available solver configs, installed on your machine.
getAvailableSolvers :: IO [SMTConfig]
getAvailableSolvers = filterM sbvCheckSolverInstallation (map defaultSolverConfig [minBound .. maxBound])

#if MIN_VERSION_template_haskell(2,22,1)
-- Starting template haskell 2.22.1 the following instances are automatically provided
#else
deriving instance TH.Lift TH.OccName
deriving instance TH.Lift TH.NameSpace
deriving instance TH.Lift TH.PkgName
deriving instance TH.Lift TH.ModName
deriving instance TH.Lift TH.NameFlavour
deriving instance TH.Lift TH.Name
deriving instance TH.Lift TH.Type
deriving instance TH.Lift TH.Specificity
deriving instance TH.Lift (TH.TyVarBndr TH.Specificity)
deriving instance TH.Lift (TH.TyVarBndr ())
deriving instance TH.Lift TH.TyLit
#endif

-- A few other things we need to TH lift
deriving instance TH.Lift Kind

-- | What kind of type is this?
data ADT = ADTEnum [TH.Name]                      -- Enumeration. If the list is empty, then an uninterpreted
         | ADTFull [(TH.Name, [(TH.Type, Kind)])] -- Constructors and fields

-- | Create a symbolic ADT
mkSymbolic :: TH.Name -> TH.Q [TH.Dec]
mkSymbolic typeName = do

     tKind <- dissect typeName

     case tKind of
       ADTEnum cs    -> mkEnum typeName cs      -- also handles uninterpreted types
       ADTFull cstrs -> mkADT  typeName cstrs

-- | Make an uninterpreted or enumeration type
mkEnum :: TH.Name -> [TH.Name] -> TH.Q [TH.Dec]
mkEnum typeName cstrs = do
    let typeCon  = TH.conT typeName
        sTypeCon = TH.conT ''SBV `TH.appT` typeCon

        -- Is this an enum?
        isEnum = not (null cstrs)

    derives <- [d| deriving instance Show     $typeCon
                   deriving instance Read     $typeCon
                   deriving instance Data     $typeCon
                   deriving instance HasKind  $typeCon
                   deriving instance SatModel $typeCon
               |]

    symVals <- if isEnum
                  then [d| instance SymVal $typeCon where
                             minMaxBound = Just (minBound, maxBound)

                           instance Arbitrary $typeCon where
                             arbitrary = arbitraryBoundedEnum
                       |]
                  else [d| instance SymVal $typeCon where
                             minMaxBound = Nothing

                           -- It's unfortunate we have to give this instance to make things
                           -- simple; but uninterpreted types don't really fit with the testing strategy.
                           instance {-# OVERLAPPABLE #-} Arbitrary $typeCon where
                             arbitrary = error $ unlines [ ""
                                                         , "*** Data.SBV: Cannot quickcheck the given property."
                                                         , "***"
                                                         , "*** Default arbitrary instance for " ++ TH.nameBase typeName ++ " is too limited."
                                                         , "***"
                                                         , "*** You can overcome this by giving your own Arbitrary instance."
                                                         , "*** Please get in touch if this workaround is not suitable for your case."
                                                         ]
                       |]

    symEnum <- if isEnum
                  then [d| instance SL.EnumSymbolic $typeCon where
                              succ     x = let elts = [minBound .. maxBound] in x `SL.lookup` literal (zip elts (drop 1 elts))
                              pred     x = let elts = [minBound .. maxBound] in x `SL.lookup` literal (zip (drop 1 elts) elts)

                              toEnum   x = let elts = [minBound .. maxBound] in x `SL.lookup` literal (zip [0..] elts)
                              fromEnum x = let elts = [minBound .. maxBound] in x `SL.lookup` literal (zip elts [0..])

                              enumFrom n = SL.map SL.toEnum (SL.enumFromTo (SL.fromEnum n) (SL.fromEnum (literal (maxBound :: $typeCon))))

                              enumFromThen = smtFunction ("EnumSymbolic." ++ TH.nameBase typeName ++ ".enumFromThen") $ \n1 n2 ->
                                                         let i_n1, i_n2 :: SInteger
                                                             i_n1 = SL.fromEnum n1
                                                             i_n2 = SL.fromEnum n2
                                                         in SL.map SL.toEnum (ite (i_n2 .>= i_n1)
                                                                                  (SL.enumFromThenTo i_n1 i_n2 (SL.fromEnum (literal (maxBound :: $typeCon))))
                                                                                  (SL.enumFromThenTo i_n1 i_n2 (SL.fromEnum (literal (minBound :: $typeCon)))))

                              enumFromTo     n m   = SL.map SL.toEnum (SL.enumFromTo     (SL.fromEnum n) (SL.fromEnum m))

                              enumFromThenTo n m t = SL.map SL.toEnum (SL.enumFromThenTo (SL.fromEnum n) (SL.fromEnum m) (SL.fromEnum t))

                           instance OrdSymbolic $sTypeCon where
                             SBV a .<  SBV b = SBV (a `svLessThan`    b)
                             SBV a .<= SBV b = SBV (a `svLessEq`      b)
                             SBV a .>  SBV b = SBV (a `svGreaterThan` b)
                             SBV a .>= SBV b = SBV (a `svGreaterEq`   b)
                       |]
                  else pure []

    sType <- sTypeCon

    let declConstructor c = ((nm, bnm), [sig, def])
          where bnm  = TH.nameBase c
                nm   = TH.mkName $ 's' : bnm
                def  = TH.FunD nm [TH.Clause [] (TH.NormalB body) []]
                body = TH.AppE (TH.VarE 'literal) (TH.ConE c)
                sig  = TH.SigD nm sType

        (constrNames, cdecls) = unzip (map declConstructor cstrs)

    let btname = TH.nameBase typeName
        tname  = TH.mkName ('S' : btname)
        tdecl  = TH.TySynD tname [] sType

    addDeclDocs (tname, btname) constrNames

    -- Declare testers and case analyzer, if this is an enumeration
    testsAndCase <- if isEnum
                    then do ts <- mkTesters sType (map (, []) cstrs)
                            (caseSig, caseFun) <- mkCaseAnalyzer typeName (map (, []) cstrs)
                            pure $ caseSig : caseFun : ts
                    else pure []

    pure $ derives ++ symVals ++ symEnum ++ [tdecl] ++ concat cdecls ++ testsAndCase

-- | Add document to a generated declaration for the declaration
addDeclDocs :: (TH.Name, String) -> [(TH.Name, String)] -> TH.Q ()
#if MIN_VERSION_template_haskell(2,18,0)
addDeclDocs (tnm, ts) cnms = do add True (tnm, ts)
                                mapM_  (add False) cnms
   where add True  (cnm, cs) = TH.addModFinalizer $ TH.putDoc (TH.DeclDoc cnm) $ "Symbolic version of the type '"        ++ cs ++ "'."
         add False (cnm, cs) = TH.addModFinalizer $ TH.putDoc (TH.DeclDoc cnm) $ "Symbolic version of the constructor '" ++ cs ++ "'."
#else
addDeclDocs _ _ = pure ()
#endif

-- | Add document to a generated function
addDoc :: String -> TH.Name -> TH.Q ()
#if MIN_VERSION_template_haskell(2,18,0)
addDoc what tnm = TH.addModFinalizer $ TH.putDoc (TH.DeclDoc tnm) what
#else
addDoc _ _ = pure ()
#endif

-- | Symbolic version of a type
mkSBV :: TH.Type -> TH.Type
mkSBV a = TH.ConT ''SBV `TH.AppT` a

-- | Create a symbolic ADT
mkADT :: TH.Name -> [(TH.Name, [(TH.Type, Kind)])] -> TH.Q [TH.Dec]
mkADT typeName cstrs = do

    let typeCon = TH.ConT typeName
        sType   = mkSBV typeCon

    litFun <- do let mkLitClause (n, fs) = do as <- mapM (const (TH.newName "a")) fs
                                              let cn      = TH.mkName $ 's' : TH.nameBase n
                                                  app a b = TH.AppE a (TH.AppE (TH.VarE 'literal) b)
                                              pure $ TH.Clause [TH.ConP n [] (map TH.VarP as)]
                                                               (TH.NormalB (foldl app (TH.VarE cn) (map TH.VarE as)))
                                                               []
                 TH.FunD 'literal <$> mapM mkLitClause cstrs

    fromCVFunName <- TH.newName ("fromCV_" ++ TH.nameBase typeName)
    let fromCVSig = TH.SigD fromCVFunName (foldr (TH.AppT . TH.AppT TH.ArrowT) typeCon [TH.ConT ''String, TH.AppT TH.ListT (TH.ConT ''CV)])

        fromCVCls :: (TH.Name, [(TH.Type, Kind)]) -> TH.Q TH.Clause
        fromCVCls (nm, args) = do
            ns <- mapM (\(i, _) -> TH.newName ("a" ++ show i)) (zip [(1::Int)..] args)
            let pat = foldr ((\p acc -> TH.ConP '(:) [] [p, acc]) . TH.VarP) (TH.ConP '[] [] []) ns
            pure $ TH.Clause [TH.LitP (TH.StringL (TH.nameBase nm)), pat]
                             (TH.NormalB (foldl TH.AppE (TH.ConE nm)
                                                        [TH.AppE (TH.VarE 'fromCV) (TH.VarE n) | n <- ns]))
                             []

    catchAll <- do s <- TH.newName "s"
                   l <- TH.newName "l"
                   let errStr   = TH.LitE (TH.StringL ("fromCV " ++ TH.nameBase typeName ++ ": Unexpected constructor/arity: "))
                       tup      = TH.TupE [Just (TH.VarE s), Just (TH.AppE (TH.VarE 'length) (TH.VarE l))]
                       showCall = TH.AppE (TH.VarE 'show) tup
                       errMsg   = TH.InfixE (Just errStr) (TH.VarE '(++)) (Just showCall)
                   pure $ TH.Clause [TH.VarP s, TH.VarP l] (TH.NormalB (TH.AppE (TH.VarE 'error) errMsg)) []

    fromCVFun <- do clss <- mapM fromCVCls cstrs
                    pure $ TH.FunD fromCVFunName (clss ++ [catchAll])

    getFromCV <- [| let unexpected w = error $ "fromCV: " ++ show typeName ++ ": " ++ w
                        fixRef kRef (KADT curName Nothing) | curName == unmod typeName = kRef
                        fixRef _    k                                                  = k
                    in \case CV kTop@(KADT _ (Just fks)) (CADT (c, vs)) ->
                                 case c `lookup` fks of
                                   Nothing  -> unexpected $ "Cannot find constructor in kind: " ++ show (c, fks)
                                   Just ks
                                     | length ks /= length vs
                                     -> unexpected $ "Mismatching arity for " ++ show typeName ++ " " ++ show (c, length ks, length vs)
                                     | True
                                     -> $(TH.varE fromCVFunName) c (zipWith CV (map (fixRef kTop) ks) vs)
                             CV k _ -> unexpected $ "Was expecting a CADT value, but got kind: " ++ show k
                 |]

    let symVal = TH.InstanceD Nothing [] (TH.AppT (TH.ConT ''SymVal) typeCon)
                                         [ litFun
                                         , TH.FunD 'minMaxBound [TH.Clause [] (TH.NormalB (TH.ConE 'Nothing)) []]
                                         , TH.FunD 'fromCV      [TH.Clause [] (TH.NormalB getFromCV)          []]
                                         ]

    decls <- [d|instance HasKind $(pure typeCon) where
                  kindOf _ = KADT (unmod typeName) (Just [(unmod n, map snd tks) | (n, tks) <- cstrs])

                instance {-# OVERLAPPABLE #-} Arbitrary $(pure typeCon) where
                   arbitrary = error $ unlines [ ""
                                               , "*** Data.SBV: Cannot quickcheck the given property."
                                               , "***"
                                               , "*** Default arbitrary instance for " ++ TH.nameBase typeName ++ " is too limited."
                                               , "***"
                                               , "*** You can overcome this by giving your own Arbitrary instance."
                                               , "*** Please get in touch if this workaround is not suitable for your case."
                                               ]
             |]

    -- Declare constructors
    let declConstructor :: (TH.Name, [(TH.Type, Kind)]) -> ((TH.Name, String), [TH.Dec])
        declConstructor (c, tks) = let ats = map (mkSBV . fst) tks
                                       ty  = foldr (TH.AppT . TH.AppT TH.ArrowT) sType ats
                                   in ((nm, bnm), [TH.SigD nm ty, def])
          where bnm  = TH.nameBase c
                nm   = TH.mkName $ 's' : bnm
                def  = TH.FunD nm [TH.Clause [] (TH.NormalB body) []]
                body = TH.AppE (TH.VarE 'mkConstructor) (TH.LitE (TH.StringL bnm))

    let (constrNames, cdecls) = unzip $ map declConstructor cstrs

    let btname = TH.nameBase typeName
        tname  = TH.mkName ('S' : btname)
        tdecl  = TH.TySynD tname [] sType

    addDeclDocs (tname, btname) constrNames

    -- Declare accessors
    let declAccessor :: TH.Name -> (TH.Type, Kind) -> Int -> ((TH.Name, String), [TH.Dec])
        declAccessor c (ft, _) i = let ty = TH.AppT (TH.AppT TH.ArrowT sType) (mkSBV ft)
                                   in ((nm, bnm), [TH.SigD nm ty, def])
          where bnm  = TH.nameBase c
                anm  = "get" ++ bnm ++ "_" ++ show i
                nm   = TH.mkName anm
                def  = TH.FunD nm [TH.Clause [] (TH.NormalB body) []]
                body = TH.AppE (TH.VarE 'mkConstructor) (TH.LitE (TH.StringL anm))

    let (accessorNames, accessorDecls) = unzip $ concat [zipWith (declAccessor c) fs [(1::Int) ..] | (c, fs) <- cstrs]

    mapM_ (addDoc "Accessor" . fst) accessorNames

    -- Declare testers
    testerDecls <- mkTesters sType cstrs

    -- Get the case analyzer
    (caseSig, caseFun) <- mkCaseAnalyzer typeName cstrs

    pure $ tdecl : symVal : decls ++ concat cdecls ++ testerDecls ++ concat accessorDecls ++ [caseSig, caseFun] ++ [fromCVSig, fromCVFun]

-- | Make a case analyzer for the type. Works for ADTs and enums. Returns sig and defn
mkCaseAnalyzer :: TH.Name -> [(TH.Name, [(TH.Type, Kind)])] -> TH.Q (TH.Dec, TH.Dec)
mkCaseAnalyzer typeName cstrs = do
        let typeCon = TH.ConT typeName
            sType   = mkSBV typeCon

            bnm = TH.nameBase typeName
            cnm = TH.mkName $ "sCase" ++ bnm

        se   <- TH.newName ('s' : bnm)
        fs   <- mapM (\(nm, _) -> TH.newName ('f' : TH.nameBase nm)) cstrs
        res  <- TH.newName "result"

        let def = TH.FunD cnm [TH.Clause (map TH.VarP (se : fs)) (TH.NormalB (iteChain (zipWith (mkCase se) fs cstrs))) []]

            iteChain :: [(TH.Exp, TH.Exp)] -> TH.Exp
            iteChain []       = error $ unlines [ "Data.SBV.mkADT: Impossible happened!"
                                                , ""
                                                , "   Received an empty list for: " ++ show typeName
                                                , ""
                                                , "While building the case-analyzer."
                                                , "Please report this as a bug."
                                                ]
            iteChain [(_, l)]        = l
            iteChain ((t, e) : rest) = foldl TH.AppE (TH.VarE 'ite) [TH.AppE t (TH.VarE se), e, iteChain rest]

            mkCase :: TH.Name -> TH.Name -> (TH.Name, [(TH.Type, Kind)]) -> (TH.Exp, TH.Exp)
            mkCase cexpr func (c, fields) = (TH.VarE (TH.mkName ("is" ++ TH.nameBase c)), foldl TH.AppE (TH.VarE func) args)
               where getters = [TH.mkName ("get" ++ TH.nameBase c ++ "_" ++ show i) | (i, _) <- zip [(1 :: Int) ..] fields]
                     args    = map (\g -> TH.AppE (TH.VarE g) (TH.VarE cexpr)) getters

            rvar   = TH.VarT res
            mkFun  = foldr (TH.AppT . TH.AppT TH.ArrowT) rvar
            fTypes = [mkFun (map (mkSBV . fst) ftks) | (_, ftks) <- cstrs]
            sig    = TH.SigD cnm (TH.ForallT [TH.PlainTV res TH.SpecifiedSpec]
                                             [TH.AppT (TH.ConT ''Mergeable) (TH.VarT res)]
                                             (mkFun (sType : fTypes)))

        pure (sig, def)

-- | Declare testers
mkTesters :: TH.Type -> [(TH.Name, [(TH.Type, Kind)])] -> TH.Q [TH.Dec]
mkTesters sType cstrs = do
    let declTester :: (TH.Name, [(TH.Type, Kind)]) -> ((TH.Name, String), [TH.Dec])
        declTester (c, _) = let ty = TH.AppT (TH.AppT TH.ArrowT sType) (TH.ConT ''SBool)
                            in ((nm, bnm), [TH.SigD nm ty, def])
          where bnm  = TH.nameBase c
                nm   = TH.mkName $ "is" ++ bnm
                def  = TH.FunD nm [TH.Clause [] (TH.NormalB body) []]
                body = TH.AppE (TH.VarE 'mkConstructor) (TH.LitE (TH.StringL ("(_ is " ++ bnm ++ ")")))

    let (testerNames, testerDecls) = unzip $ map declTester cstrs

    mapM_ (addDoc "Tester" . fst) testerNames

    pure $ concat testerDecls

-- We'll just drop the modules to keep this simple
-- If you use multiple expressions named the same (coming from different modules), oh well.
unmod :: TH.Name -> String
unmod = reverse . takeWhile (/= '.') . reverse . show

-- | Given a type name, determine what kind of a data-type it is.
dissect :: TH.Name -> TH.Q ADT
dissect typeName = do
        tcs <- getConstructors typeName

        let mk n t = do k <- expandSyns t >>= toSBV typeName n
                        pure (t, k)

        cs  <- mapM (\(n, ts) -> (n,) <$> mapM (mk n) ts) tcs

        pure $ if all (null . snd) cs
               then ADTEnum (map fst cs)
               else ADTFull cs

bad :: MonadFail m => String -> [String] -> m a
bad what extras = fail $ unlines $ ("mkSymbolic: " ++ what) : map ("      " ++) extras

report :: String
report = "Please report this as a feature request."

-- | Collect the constructors
getConstructors :: TH.Name -> TH.Q [(TH.Name, [TH.Type])]
getConstructors typeName = getConstructorsFromType (TH.ConT typeName)
  where getConstructorsFromType :: TH.Type -> TH.Q [(TH.Name, [TH.Type])]
        getConstructorsFromType ty = do ty' <- expandSyns ty
                                        case headCon ty' of
                                          Just (n, args) -> reifyFromHead n args
                                          Nothing        -> bad "Not a type constructor"
                                                                [ "Name    : " ++ show typeName
                                                                , "Type    : " ++ show ty
                                                                , "Expanded: " ++ show ty'
                                                                ]

        headCon :: TH.Type -> Maybe (TH.Name, [TH.Type])
        headCon = go []
          where go args (TH.ConT n)    = Just (n, reverse args)
                go args (TH.AppT t a)  = go   (a:args) t
                go args (TH.SigT t _)  = go      args t
                go args (TH.ParensT t) = go      args t
                go _    _              = Nothing

        reifyFromHead :: TH.Name -> [TH.Type] -> TH.Q [(TH.Name, [TH.Type])]
        reifyFromHead n args = do info <- TH.reify n
                                  case info of
                                    TH.TyConI (TH.DataD    _ _ tvs _ cons _) -> mapM (expandCon (mkSubst tvs args)) cons
                                    TH.TyConI (TH.NewtypeD _ _ tvs _ con  _) -> mapM (expandCon (mkSubst tvs args)) [con]
                                    TH.TyConI (TH.TySynD _ tvs rhs)          -> getConstructorsFromType (applySubst (mkSubst tvs args) rhs)
                                    _ -> bad "Unsupported kind"
                                             [ "Type : " ++ show typeName
                                             , "Name : " ++ show n
                                             , "Kind : " ++ show info
                                             ]

        expandCon :: [(TH.Name, TH.Type)] -> TH.Con -> TH.Q (TH.Name, [TH.Type])
        expandCon sub (TH.NormalC  n fields)          = (n,) <$> mapM (expandSyns . applySubst sub . snd) fields
        expandCon sub (TH.RecC     n fields)          = (n,) <$> mapM (expandSyns . applySubst sub . (\(_,_,t) -> t)) fields
        expandCon sub (TH.InfixC   (_, t1) n (_, t2)) = (n,) <$> mapM (expandSyns . applySubst sub) [t1, t2]
        {- These don't have proper correspondences in SMTLib; so ignore.
        expandCon sub (TH.ForallC  _ _ c)             = expandCon sub c
        expandCon sub (TH.GadtC    [n] fields _)      = (n,) <$> mapM (expandSyns . applySubst sub . snd) fields
        expandCon sub (TH.RecGadtC [n] fields _)      = (n,) <$> mapM (expandSyns . applySubst sub . (\(_,_,t) -> t)) fields
        -}
        expandCon _   c                               = bad "Unsupported constructor form: "
                                                            [ "Type       : " ++ show typeName
                                                            , "Constructor: " ++ show c
                                                            , ""
                                                            , report
                                                            ]

        -- | Make substitution from type variables to actual args
        mkSubst :: [TH.TyVarBndr TH.BndrVis] -> [TH.Type] -> [(TH.Name, TH.Type)]
        mkSubst tvs = zip (map tvName tvs)
          where tvName (TH.PlainTV  n _)   = n
                tvName (TH.KindedTV n _ _) = n

        -- | Apply substitution to a Type
        applySubst :: [(TH.Name, TH.Type)] -> TH.Type -> TH.Type
        applySubst sub = go
          where go (TH.VarT    n)        = fromMaybe  (TH.VarT n) (n `lookup` sub)
                go (TH.AppT    t1 t2)    = TH.AppT    (go t1) (go t2)
                go (TH.SigT    t k)      = TH.SigT    (go t)  k
                go (TH.ParensT t)        = TH.ParensT (go t)
                go (TH.InfixT  t1 n t2)  = TH.InfixT  (go t1) n (go t2)
                go (TH.UInfixT t1 n t2)  = TH.UInfixT (go t1) n (go t2)
                go (TH.ForallT bs ctx t) = TH.ForallT bs (map goPred ctx) (go t)
                go t                     = t

                goPred (TH.AppT t1 t2) = TH.AppT (go t1) (go t2)
                goPred p               = p

-- | Find the SBV kind for this type
toSBV :: TH.Name -> TH.Name -> TH.Type -> TH.Q Kind
toSBV typeName constructorName = go
  where tName = unmod typeName

        go (TH.ConT c)
         | c == typeName = pure $ KADT tName Nothing -- recursive case: use site, so fields are nothing
         | True          = extract c

        -- tuples
        go t | Just ps <- getTuple t = KTuple <$> mapM go ps

        -- recognize strings, since we don't (yet) support chars
        go (TH.AppT TH.ListT (TH.ConT t)) | t == ''Char = pure KString

        -- lists
        go (TH.AppT TH.ListT t) = KList <$> go t

        -- maybe
        go (TH.AppT (TH.ConT nm) t) | nm == ''Maybe = KMaybe <$> go t

        -- either
        go (TH.AppT (TH.AppT (TH.ConT nm) t1) t2) | nm == ''Either = KEither <$> go t1 <*> go t2

        -- arbitrary words/ints
        go (TH.AppT (TH.ConT nm) (TH.LitT (TH.NumTyLit n)))
            | nm == ''WordN = pure $ KBounded False (fromIntegral n)
            | nm == ''IntN  = pure $ KBounded True  (fromIntegral n)

        -- arbitrary floats
        go (TH.AppT (TH.AppT (TH.ConT nm) (TH.LitT (TH.NumTyLit eb))) (TH.LitT (TH.NumTyLit sb)))
            | nm == ''FloatingPoint = pure $ KFP (fromIntegral eb) (fromIntegral sb)

        -- rational
        go (TH.AppT (TH.ConT nm) (TH.ConT p))
            | nm == ''Ratio && p == ''Integer = pure KRational

        -- giving up
        go t = bad "Unsupported constructor kind" [ "Datatype   : " ++ show typeName
                                                  , "Constructor: " ++ show constructorName
                                                  , "Kind       : " ++ show t
                                                  , ""
                                                  , report
                                                  ]

        -- Extract an N-tuple
        getTuple = tup []
          where tup sofar (TH.TupleT _) = Just sofar
                tup sofar (TH.AppT t p) = tup (p : sofar) t
                tup _     _             = Nothing

        -- Given the name of a type, what's the equivalent in the SBV domain?
        extract :: TH.Name -> TH.Q Kind
        extract t
          | t == ''Bool     = pure KBool
          | t == ''Integer  = pure KUnbounded
          | t == ''Float    = pure KFloat
          | t == ''Double   = pure KDouble

          -- Punt on char and rational. Because SMTLib's string translation requires us to put extra constraints.
          -- We'll do that when we get there.
          -- | t == ''Char     = pure KChar
          -- | t == ''Rational = pure KRational
          | t == ''Char || t == ''Rational
          = bad "Unsupported type: Char"
                [ "Datatype   : " ++ show typeName
                , "Constructor: " ++ show constructorName
                , "Kind       : " ++ show t
                , ""
                , "While SBV supports SChar, ADT fields with characters are not yet supported."
                , report
                ]

          | t == ''String   = pure KString
          | t == ''AlgReal  = pure KReal
          | t == ''Word8    = pure $ KBounded False  8
          | t == ''Word16   = pure $ KBounded False 16
          | t == ''Word32   = pure $ KBounded False 32
          | t == ''Word64   = pure $ KBounded False 64
          | t == ''Int8     = pure $ KBounded True   8
          | t == ''Int16    = pure $ KBounded True  16
          | t == ''Int32    = pure $ KBounded True  32
          | t == ''Int64    = pure $ KBounded True  64

          -- Platform specific: Complain
          | t == ''Int || t == ''Word
          = bad ("Unsupported platform specific type: " ++ show t)
                [ "    Datatype   : " ++ show typeName
                , "    Constructor: " ++ show constructorName
                , "    Field type : " ++ show t
                , ""
                , "Please pick a more specific type, such as Integer, Word8, WordN 32, IntN 16 etc."
                ]
          {-
           - TODO: how do we map to these?
            | KUserSort String (Maybe [String])
            | KADT      String [String]
            | KSet      Kind
            | KArray    Kind Kind
          -}
          | True
          = bad "Unsupported field type"
                [ "    Datatype   : " ++ show typeName
                , "    Constructor: " ++ show constructorName
                , "    Field type : " ++ show t
                , ""
                , report
                ]
