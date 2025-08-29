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
{-# LANGUAGE PackageImports      #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TupleSections       #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module Data.SBV.Client
  ( sbvCheckSolverInstallation
  , defaultSolverConfig
  , getAvailableSolvers
  , mkSymbolic
  ) where

import Data.Generics

import Control.Monad (filterM)
import Test.QuickCheck (Arbitrary(..), arbitraryBoundedEnum)

import qualified Control.Exception as C

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
       ADTEnum cs    -> mkEnum typeName cs
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

    addDocs (tname, btname) constrNames

    pure $ derives ++ symVals ++ symEnum ++ [tdecl] ++ concat cdecls

-- | Add document to a generated declaration
addDocs :: (TH.Name, String) -> [(TH.Name, String)] -> TH.Q ()
#if MIN_VERSION_template_haskell(2,18,0)
addDocs (tnm, ts) cnms = do addDoc True (tnm, ts)
                            mapM_  (addDoc False) cnms
   where addDoc True  (cnm, cs) = TH.addModFinalizer $ TH.putDoc (TH.DeclDoc cnm) $ "Symbolic version of the type '"        ++ cs ++ "'."
         addDoc False (cnm, cs) = TH.addModFinalizer $ TH.putDoc (TH.DeclDoc cnm) $ "Symbolic version of the constructor '" ++ cs ++ "'."
#else
addDocs _ _ = pure ()
#endif

-- | Create a symbolic ADT
mkADT :: TH.Name -> [(TH.Name, [(TH.Type, Kind)])] -> TH.Q [TH.Dec]
mkADT typeName cstrs = do
    let mkSBV :: TH.Type -> TH.Type
        mkSBV a = TH.ConT ''SBV `TH.AppT` a

        typeCon = TH.ConT typeName
        sType   = mkSBV typeCon

    decls <- [d|instance HasKind $(pure typeCon) where
                  kindOf _ = KADT (unmod typeName) (Just [(unmod n, map snd tks) | (n, tks) <- cstrs])

                instance SymVal $(pure typeCon) where
                  literal     = error "literal"
                  fromCV      = error "fromCV"
                  minMaxBound = Nothing

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

    let declConstructor :: (TH.Name, [(TH.Type, Kind)]) -> TH.Q ((TH.Name, String), [TH.Dec])
        declConstructor (c, tks) = do let ats = map (mkSBV . fst) tks
                                      let ty = foldr (\a b -> TH.AppT (TH.AppT TH.ArrowT a) b) sType ats
                                      pure ((nm, bnm), [TH.SigD nm ty, def])
          where bnm  = TH.nameBase c
                nm   = TH.mkName $ 's' : bnm
                def  = TH.FunD nm [TH.Clause [] (TH.NormalB body) []]
                body = TH.AppE (TH.VarE 'mkConstructor) (TH.LitE (TH.StringL bnm))

    (constrNames, cdecls) <- unzip <$> mapM declConstructor cstrs

    let btname = TH.nameBase typeName
        tname  = TH.mkName ('S' : btname)
        tdecl  = TH.TySynD tname [] sType

    addDocs (tname, btname) constrNames

    pure $ tdecl : decls ++ concat cdecls

-- We'll just drop the modules to keep this simple
-- If you use multiple expressions named the same (coming from different modules), oh well.
unmod :: TH.Name -> String
unmod = reverse . takeWhile (/= '.') . reverse . show

-- | Given a type name, determine what kind of a data-type it is.
dissect :: TH.Name -> TH.Q ADT
dissect typeName = do
        tcs <- getConstructors typeName

        let mk n t = do k <- expandSyns t >>= toSBV n
                        pure (t, k)

        cs  <- mapM (\(n, ts) -> (n,) <$> mapM (mk n) ts) tcs

        pure $ if all (null . snd) cs
               then ADTEnum (map fst cs)
               else ADTFull cs

  where tName = unmod typeName

        bad what extras = fail $ unlines $ ("mkSymbolic: " ++ what) : map ("      " ++) extras
        report          = "Please report this as a feature request."

        headCon :: TH.Type -> Maybe (TH.Name, [TH.Type])
        headCon = go []
          where go args (TH.ConT n)    = Just (n, reverse args)
                go args (TH.AppT t a)  = go   (a:args) t
                go args (TH.SigT t _)  = go      args t
                go args (TH.ParensT t) = go      args t
                go _    _              = Nothing

        getConstructors :: TH.Name -> TH.Q [(TH.Name, [TH.Type])]
        getConstructors topName = getConstructorsFromType (TH.ConT topName)

        getConstructorsFromType :: TH.Type -> TH.Q [(TH.Name, [TH.Type])]
        getConstructorsFromType ty = do ty' <- expandSyns ty
                                        case headCon ty' of
                                          Just (n, args) -> reifyFromHead n args
                                          Nothing        -> bad "Not a type constructor"
                                                                [ "Name    : " ++ show typeName
                                                                , "Type    : " ++ show ty
                                                                , "Expanded: " ++ show ty'
                                                                ]

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
        mkSubst tvs args = zip (map tvName tvs) args
          where tvName (TH.PlainTV  n _)   = n
                tvName (TH.KindedTV n _ _) = n

        -- | Apply substitution to a Type
        applySubst :: [(TH.Name, TH.Type)] -> TH.Type -> TH.Type
        applySubst sub = go
          where go (TH.VarT    n)        = maybe      (TH.VarT n) id (n `lookup` sub)
                go (TH.AppT    t1 t2)    = TH.AppT    (go t1) (go t2)
                go (TH.SigT    t k)      = TH.SigT    (go t)  k
                go (TH.ParensT t)        = TH.ParensT (go t)
                go (TH.InfixT  t1 n t2)  = TH.InfixT  (go t1) n (go t2)
                go (TH.UInfixT t1 n t2)  = TH.UInfixT (go t1) n (go t2)
                go (TH.ForallT bs ctx t) = TH.ForallT bs (map goPred ctx) (go t)
                go t                     = t

                goPred (TH.AppT t1 t2) = TH.AppT (go t1) (go t2)
                goPred p               = p

        -- Find the SBV kind for this type
        toSBV :: TH.Name -> TH.Type -> TH.Q Kind
        toSBV constructorName = go
          where go (TH.ConT c)
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

                  -- Punt on char. Because SMTLib's string translation requires us to put extra constraints.
                  -- We'll do that when we get there.
                  -- | t == ''Char     = pure KChar
                  | t == ''Char     = bad "Unsupported type: Char"
                                          [ "Datatype   : " ++ show typeName
                                          , "Constructor: " ++ show constructorName
                                          , "Kind       : " ++ show t
                                          , ""
                                          , "While SBV supports SChar, ADT fields with characters are not yet supported."
                                          , report
                                          ]

                  | t == ''String   = pure KString
                  | t == ''AlgReal  = pure KReal
                  | t == ''Rational = pure KRational
                  | t == ''Word8    = pure $ KBounded False  8
                  | t == ''Word16   = pure $ KBounded False 16
                  | t == ''Word32   = pure $ KBounded False 32
                  | t == ''Word64   = pure $ KBounded False 64
                  | t == ''Int8     = pure $ KBounded True   8
                  | t == ''Int16    = pure $ KBounded True  16
                  | t == ''Int32    = pure $ KBounded True  32
                  | t == ''Int64    = pure $ KBounded True  64
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
