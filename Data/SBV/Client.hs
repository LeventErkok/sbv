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

{-# LANGUAGE PackageImports      #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Client
  ( sbvCheckSolverInstallation
  , defaultSolverConfig
  , sbvAvailableSolvers
  , mkSymbolicEnumeration
  , mkUninterpretedSort
  ) where

import Control.Monad (filterM)
import Data.Generics

import qualified Control.Exception   as C

import qualified "template-haskell" Language.Haskell.TH as TH

import Data.SBV.Core.Data
import Data.SBV.Core.Model
import Data.SBV.Provers.Prover

-- | Check whether the given solver is installed and is ready to go. This call does a
-- simple call to the solver to ensure all is well.
sbvCheckSolverInstallation :: SMTConfig -> IO Bool
sbvCheckSolverInstallation cfg = check `C.catch` (\(_ :: C.SomeException) -> return False)
  where check = do ThmResult r <- proveWith cfg $ \x -> (x+x) .== ((x*2) :: SWord8)
                   case r of
                     Unsatisfiable{} -> return True
                     _               -> return False

-- | The default configs corresponding to supported SMT solvers
defaultSolverConfig :: Solver -> SMTConfig
defaultSolverConfig Z3        = z3
defaultSolverConfig Yices     = yices
defaultSolverConfig Boolector = boolector
defaultSolverConfig CVC4      = cvc4
defaultSolverConfig MathSAT   = mathSAT
defaultSolverConfig ABC       = abc

-- | Return the known available solver configs, installed on your machine.
sbvAvailableSolvers :: IO [SMTConfig]
sbvAvailableSolvers = filterM sbvCheckSolverInstallation (map defaultSolverConfig [minBound .. maxBound])

-- | Turn a name into a symbolic type. If first argument is true, we'll also derive Eq and Ord instances.
declareSymbolic :: Bool -> TH.Name -> TH.Q [TH.Dec]
declareSymbolic isEnum typeName = do
    let typeCon = TH.conT typeName

    if isEnum then ensureEnumeration typeName
              else ensureEmptyData   typeName

    deriveEqOrds <- if isEnum
                       then [d| deriving instance Eq       $(typeCon)
                                deriving instance Ord      $(typeCon)
                            |]
                       else pure []

    derives <- [d| deriving instance Show     $(typeCon)
                   deriving instance Read     $(typeCon)
                   deriving instance Data     $(typeCon)
                   deriving instance SymVal   $(typeCon)
                   deriving instance HasKind  $(typeCon)
                   deriving instance SatModel $(typeCon)
               |]

    tdecl <- TH.TySynD (TH.mkName ('S' : TH.nameBase typeName)) [] <$> TH.conT ''SBV `TH.appT` typeCon
    pure $ deriveEqOrds ++ derives ++ [tdecl]

-- | Make an enumeration a symbolic type.
mkSymbolicEnumeration :: TH.Name -> TH.Q [TH.Dec]
mkSymbolicEnumeration = declareSymbolic True

-- | Make an uninterpred sort.
mkUninterpretedSort :: TH.Name -> TH.Q [TH.Dec]
mkUninterpretedSort = declareSymbolic False

-- | Make sure the given type is an enumeration
ensureEnumeration :: TH.Name -> TH.Q ()
ensureEnumeration nm = do
        c <- TH.reify nm
        case c of
          TH.TyConI d -> case d of
                           TH.DataD _ _ _ _ cons _ -> case cons of
                                                        [] -> bad "The datatype given has no constructors."
                                                        xs -> mapM_ check xs
                           _                       -> bad "The name given is not a datatype."

          _        -> bad "The name given is not a datatype."
 where n = TH.nameBase nm

       check (TH.NormalC c xs) = case xs of
                                   [] -> pure ()
                                   _  -> bad $ "Constructor " ++ show c ++ " has arguments."

       check c                 = bad $ "Constructor " ++ show c ++ " is not an enumeration value."

       bad m = TH.reportError $ unlines [ "Data.SBV.mkSymbolicEnumeration: Invalid argument " ++ show n
                                        , ""
                                        , "    Expected an enumeration. " ++ m
                                        , ""
                                        , "    To create an enumerated sort, use a simple Haskell enumerated type."
                                        ]

-- | Make sure the given type is an empty data
ensureEmptyData :: TH.Name -> TH.Q ()
ensureEmptyData nm = do
        c <- TH.reify nm
        case c of
          TH.TyConI d -> case d of
                           TH.DataD _ _ _ _ cons _ -> case cons of
                                                        [] -> pure ()
                                                        _  -> bad "The datatype given has constructors."
                           _                       -> bad "The name given is not a datatype."

          _        -> bad "The name given is not a datatype."
 where n = TH.nameBase nm
       bad m = TH.reportError $ unlines [ "Data.SBV.mkUninterpretedSort: Invalid argument " ++ show n
                                        , ""
                                        , "    Expected an empty datatype. " ++ m
                                        , ""
                                        , "    To create an uninterpreted sort, use an empty datatype declaration."
                                        ]
