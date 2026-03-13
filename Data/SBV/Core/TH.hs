-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Core.TH
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Template Haskell utilities for extracting constructor information from
-- algebraic data types. Factored out to avoid circular dependencies.
-----------------------------------------------------------------------------

{-# LANGUAGE LambdaCase              #-}
{-# LANGUAGE PackageImports          #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TemplateHaskellQuotes   #-}
{-# LANGUAGE TupleSections           #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Core.TH (
         getConstructors
       , bad
       , report
       , sbvName
       ) where

import Data.Maybe (fromMaybe)

import qualified "template-haskell" Language.Haskell.TH        as TH
import           "template-haskell" Language.Haskell.TH.Syntax as THS (Name(..), OccName(..), NameFlavour(..), PkgName, ModName(..), NameSpace(..))

import Language.Haskell.TH.ExpandSyns as TH

import Data.SBV.Core.Kind (smtType)

-- | Construct a TH 'Name' for a value\/function in the @sbv@ package, given
-- the fully qualified module name and the unqualified identifier. This avoids
-- importing the target module (which would create import cycles) while still
-- producing exact 'NameG' names that resolve correctly in generated TH splices.
sbvName :: String -> String -> TH.Name
sbvName modNm fnNm = THS.Name (THS.OccName fnNm) (THS.NameG THS.VarName sbvPkg (THS.ModName modNm))
  where -- Extract the package key from a known cross-module name in the sbv package
        sbvPkg :: THS.PkgName
        sbvPkg = case 'smtType of
                   THS.Name _ (THS.NameG _ pkg _) -> pkg
                   _                              -> error "Data.SBV.Core.TH.sbvName: unexpected name flavour"

bad :: MonadFail m => String -> [String] -> m a
bad what extras = fail $ unlines $ ("mkSymbolic: " ++ what) : map ("      " ++) extras

report :: String
report = "Please report this as a feature request."

-- | Collect the constructors
getConstructors :: TH.Name -> TH.Q ([TH.Name], [(TH.Name, [(Maybe TH.Name, TH.Type)])])
getConstructors typeName = do res@(_, cstrs) <- getConstructorsFromType (TH.ConT typeName)

                              -- make sure accessors are unique
                              let noDup [] = pure ()
                                  noDup (n:ns)
                                    | n `elem` ns = bad "Unsupported field accessor definition."
                                                        [ "Multiply used: " ++ TH.nameBase n
                                                        , ""
                                                        , "SBV does not support cases where accessor fields are replicated."
                                                        , "Please use each accessor only once."
                                                        ]
                                    | True        = noDup ns
                              noDup [n | (_, fs) <- cstrs, (Just n, _) <- fs]

                              pure res

  where getConstructorsFromType :: TH.Type -> TH.Q ([TH.Name], [(TH.Name, [(Maybe TH.Name, TH.Type)])])
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

        reifyFromHead :: TH.Name -> [TH.Type] -> TH.Q ([TH.Name], [(TH.Name, [(Maybe TH.Name, TH.Type)])])
        reifyFromHead n args = do info <- TH.reify n
                                  case info of
                                    TH.TyConI (TH.DataD    _ _ tvs _ cons _) -> (map tvName tvs,) <$> mapM (expandCon (mkSubst tvs args)) cons
                                    TH.TyConI (TH.NewtypeD _ _ tvs _ con  _) -> (map tvName tvs,) <$> mapM (expandCon (mkSubst tvs args)) [con]
                                    TH.TyConI (TH.TySynD _ tvs rhs)          -> getConstructorsFromType (applySubst (mkSubst tvs args) rhs)
                                    _ -> bad "Unsupported kind"
                                             [ "Type : " ++ show typeName
                                             , "Name : " ++ show n
                                             , "Kind : " ++ show info
                                             ]

        onSnd f (a, b) = (a,) <$> f b

        expandCon :: [(TH.Name, TH.Type)] -> TH.Con -> TH.Q (TH.Name, [(Maybe TH.Name, TH.Type)])
        expandCon sub (TH.NormalC  n fields)          = (n,) <$> mapM (onSnd (expandSyns . applySubst sub) . (\(   _,t) -> (Nothing, t))) fields
        expandCon sub (TH.RecC     n fields)          = (n,) <$> mapM (onSnd (expandSyns . applySubst sub) . (\(fn,_,t) -> (Just fn, t))) fields
        expandCon sub (TH.InfixC   (_, t1) n (_, t2)) = (n,) <$> mapM (onSnd (expandSyns . applySubst sub)) [(Nothing, t1), (Nothing, t2)]
        {- These don't have proper correspondences in SMTLib; so ignore.
        expandCon sub (TH.ForallC  _ _ c)             = expandCon sub c
        expandCon sub (TH.GadtC    [n] fields _)      = (n,) <$> mapM (onSnd (expandSyns . applySubst sub) . (\(   _,t) -> (Nothing, t))) fields
        expandCon sub (TH.RecGadtC [n] fields _)      = (n,) <$> mapM (onSnd (expandSyns . applySubst sub) . (\(fn,_,t) -> (Just fn, t))) fields
        -}
        expandCon _   c                               = bad "Unsupported constructor form: "
                                                            [ "Type       : " ++ show typeName
                                                            , "Constructor: " ++ show c
                                                            , ""
                                                            , report
                                                            ]

        tvName :: TH.TyVarBndr TH.BndrVis -> TH.Name
        tvName (TH.PlainTV  n _)   = n
        tvName (TH.KindedTV n _ _) = n

        -- | Make substitution from type variables to actual args
        mkSubst :: [TH.TyVarBndr TH.BndrVis] -> [TH.Type] -> [(TH.Name, TH.Type)]
        mkSubst tvs = zip (map tvName tvs)

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
