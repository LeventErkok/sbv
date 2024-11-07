-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.WeakestPreconditions.Length
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proof of correctness of an imperative list-length algorithm, using weakest
-- preconditions. Illustrates the use of SBV's symbolic lists together with
-- the WP algorithm.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE TypeFamilies          #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.WeakestPreconditions.Length where

import Data.SBV
import Data.SBV.Tools.WeakestPreconditions

import qualified Data.SBV.List as L

import GHC.Generics (Generic)

-- * Program state

-- | The state of the length program, paramaterized over the element type @a@
data LenS a b = LenS { xs :: a  -- ^ The input list
                     , ys :: a  -- ^ Copy of input
                     , l  :: b  -- ^ Running length
                     }
                     deriving (Generic, Mergeable)

-- | Show instance: A simplified version of what would otherwise be generated.
instance (SymVal a, Show (f a), Show b) => Show (LenS (f a) b) where
  show LenS{xs, ys, l} = "{xs = " ++ show xs ++ ", ys = " ++ show ys ++ ", l = " ++ show l ++ "}"

-- | Injection/projection from concrete and symbolic values.
instance Queriable IO (LenS (SList Integer) SInteger) where
  type QueryResult (LenS (SList Integer) SInteger) = LenS [Integer] Integer

  create                 = LenS <$> freshVar_  <*> freshVar_  <*> freshVar_
  project (LenS xs ys l) = LenS <$> project xs <*> project ys <*> project l
  embed   (LenS xs ys l) = LenS <$> embed   xs <*> embed   ys <*> embed   l

-- | Helper type synonym
type S = LenS (SList Integer) SInteger

-- * The algorithm

-- | The imperative length algorithm:
--
-- @
--    ys = xs
--    l  = 0
--    while not (null ys)
--      l  = l+1
--      ys = tail ys
-- @
--
-- Note that we need to explicitly annotate each loop with its invariant and the termination
-- measure. For convenience, we take those two as parameters, so we can experiment later.
algorithm :: Invariant S -> Maybe (Measure S) -> Stmt S
algorithm inv msr = Seq [ Assign $ \st@LenS{xs} -> st{ys = xs, l = 0}
                        , While "! (null ys)"
                                inv
                                msr
                                (\LenS{ys} -> sNot (L.null ys))
                                $ Seq [ Assign $ \st@LenS{l}  -> st{l  = l + 1  }
                                      , Assign $ \st@LenS{ys} -> st{ys = L.tail ys}
                                      ]
                        ]

-- | Precondition for our program. Nothing! It works for all lists.
pre :: S -> SBool
pre _ = sTrue

-- | Postcondition for our program: @l@ must be the length of the input list.
post :: S -> SBool
post LenS{xs, l} = l .== L.length xs

-- | Stability condition: Program must leave @xs@ unchanged.
noChange :: Stable S
noChange = [stable "xs" xs]

-- | A program is the algorithm, together with its pre- and post-conditions.
imperativeLength :: Invariant S -> Maybe (Measure S) -> Program S
imperativeLength inv msr = Program { setup         = return ()
                                   , precondition  = pre
                                   , program       = algorithm inv msr
                                   , postcondition = post
                                   , stability     = noChange
                                   }

-- | The invariant simply relates the length of the input to the length of the
-- current suffix and the length of the prefix traversed so far.
invariant :: Invariant S
invariant LenS{xs, ys, l} = L.length xs .== l + L.length ys

-- | The measure is obviously the length of @ys@, as we peel elements off of it through the loop.
measure :: Measure S
measure LenS{ys} = [L.length ys]

-- * Correctness

-- | We check that @l@ is the length of the input list @xs@ upon termination.
-- Note that even though this is an inductive proof, it is fairly easy to prove with our SMT based
-- technology, which doesn't really handle induction at all!  The usual inductive proof steps are baked
-- into the invariant establishment phase of the WP proof. We have:
--
-- >>> correctness
-- Total correctness is established.
-- Q.E.D.
correctness :: IO ()
correctness = print =<< wpProveWith defaultWPCfg{wpVerbose=True} (imperativeLength invariant (Just measure))
