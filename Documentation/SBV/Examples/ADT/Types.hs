-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.ADT.Types
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- An encoding of the simple type-checking via constraints, following
-- <https://microsoft.github.io/z3guide/docs/theories/Datatypes/#using-datatypes-for-solving-type-constraints>
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall -Werror #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

module Documentation.SBV.Examples.ADT.Types where

import Data.SBV

-- | Simple encoding of untyped lambda terms
data M = Var { var   :: String }     -- ^ Variables: @x@
       | Lam { bound :: String       -- ^ Abstraction: @\x. M@
             , body :: M
             }
       | App { fn  :: M              -- ^ Application: @M M@
             , arg :: M
             }

-- | Types.
data T = TInt                        -- ^ Integers
       | TStr                        -- ^ Strings
       | TArr { dom :: T, rng :: T } -- ^ Functions: @t -> t@

-- | Make terms and types symbolic
mkSymbolic [''M]
mkSymbolic [''T]

-- | Instead of modeling environments for mapping variables to their
-- types, we'll simply use an uninterpreted function. Note that
-- this also implies we consider all terms to be given so that variables
-- do not shadow each other; i.e., all variables are unique. This is
-- a simplification, but it is not without justification: One can 
-- always alpha-rename bound variables so all bound variables are unique.
env :: SString -> ST
env = uninterpret "env"

-- | Use an uninterpreted function to also magically find the type of a term.
typeOf :: SM -> ST
typeOf = uninterpret "typeOf"

-- | Given a term and a type, check that the term has that type.
tc :: SM -> ST -> SBool
tc = smtFunction "constraints" $ \m t ->
        [sCase|M m of

          -- Var case. The environment must match the type we expect.
          Var s -> env s .== t

          -- Abstraction case. Type must be a function, whose domain matches the variable.
          -- And body much match the range. Note that we can't do a nested scase
          -- here, unfortunately, since custom quasi-quoters do not nest.
          Lam v b
            | isTArr t .&& env v .== sdom t
            -> tc b (srng t)

          -- Application case. In this case, we ask the solver to give us the type of the
          -- function, and then ensure the whole thing is well-formedvx
          App f a -> let tf = typeOf f
                     in   isTArr tf      -- f must have an arrow type
                      .&& tc f tf        -- The function must type-check with that type
                      .&& tc a (sdom tf) -- Argument must have the type of this function
                      .&& t .== srng tf  -- Final result must match the type we're looking for

          -- Otherwise, ill-typed.
          _ -> sFalse
        |]

-- | Well typedness: If what the 'typeOf' function returns type-checks the term,
-- then a term is well-typed.
wellTyped :: SM -> SBool
wellTyped m = tc m (typeOf m)

-- | Make sure the identity function can be typed.
--
-- >>> idWF
-- Satisfiable. Model:
--   env :: String -> T
--   env _ = TInt
-- <BLANKLINE>
--   typeOf :: M -> T
--   typeOf _ = TArr TInt TInt
--
-- The model is rather uninteresting, but it shows that identity can have the type Integer to Integer, where
-- all variables are mapped to Integers.
idWF :: IO SatResult
idWF = sat $ wellTyped $ sLam x vx
  where x  = literal "x"
        vx = sVar x

-- | Check that if we apply a function that takes n integer to a string is not well-typed.
--
-- >>> intFuncAppString
-- Unsatisfiable
--
-- As expected, the solver says that there's no way to type-check such an expression.
intFuncAppString :: IO SatResult
intFuncAppString = sat $ do
        -- Introduce the constant @plus1 :: Int -> Int@
        plus1 <- free "plus1"
        constrain $ tc plus1 (literal (TInt `TArr` TInt))

        -- Introduce the constant @str :: String@
        str <- free "str"
        constrain $ tc str sTStr

        -- Check if the application of plus1 to str can be well-typed
        pure $ wellTyped $ sApp plus1 str

-- | Make sure self-application cannot be typed.
--
-- >>> selfAppNotWellTyped
-- Unsatisfiable
--
-- We get unsatisfiable, indicating there's no way to come up with an environment that will
-- successfully assign a type to the term @\x -> x x@.
selfAppNotWellTyped :: IO SatResult
selfAppNotWellTyped = sat $ wellTyped $ sLam x (sApp vx vx)
  where x  = literal "x"
        vx = sVar x
