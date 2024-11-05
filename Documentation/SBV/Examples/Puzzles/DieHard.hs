-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.DieHard
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Solves the die-hard riddle: In the movie Die Hard 3, the heroes must obtain
-- exactly 4 gallons of water using a 5 gallon jug, a 3 gallon jug, and a water faucet.
-- We use a bounded-model-checking style search to find a solution.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE OverloadedRecordDot   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.DieHard where

import Data.SBV
import Data.SBV.Control
import Data.SBV.Tools.BMC

-- | Possible actions
data Action = Initial | FillBig | FillSmall | EmptyBig | EmptySmall | BigToSmall | SmallToBig

mkSymbolicEnumeration ''Action

-- | We represent the state with two quantities, the amount of water in each jug. The
-- action is how we got into this state.
data State a b = State { big    :: a
                       , small  :: a
                       , action :: b
                       }

-- | Show instance
instance (Show a, Show b) => Show (State a b) where
  show s = "Big: " ++ show s.big ++ ", Small: " ++ show s.small ++ " (" ++ show s.action ++ ")"

-- | Fully symbolic state
type SState = State SInteger SAction

-- | Fully concrete state
type CState = State Integer  Action

-- | 'Queriable' instance needed for running bmc
instance Queriable IO SState where
  type QueryResult SState = CState

  create = State <$> freshVar_ <*> freshVar_ <*> freshVar_

  project State{big, small, action} = do b <- getValue big
                                         s <- getValue small
                                         a <- getValue action
                                         pure State{ big    = b
                                                   , small  = s
                                                   , action = a
                                                   }

  embed State{big, small, action} = pure State{ big    = literal big
                                              , small  = literal small
                                              , action = literal action
                                              }

-- | Solve the problem using a BMC search. We have:
--
-- >>> dieHard
-- BMC Cover: Iteration: 0
-- BMC Cover: Iteration: 1
-- BMC Cover: Iteration: 2
-- BMC Cover: Iteration: 3
-- BMC Cover: Iteration: 4
-- BMC Cover: Iteration: 5
-- BMC Cover: Iteration: 6
-- BMC Cover: Solution found at iteration 6
-- Big: 0, Small: 0 (Initial)
-- Big: 5, Small: 0 (FillBig)
-- Big: 2, Small: 3 (BigToSmall)
-- Big: 2, Small: 0 (EmptySmall)
-- Big: 0, Small: 2 (BigToSmall)
-- Big: 5, Small: 2 (FillBig)
-- Big: 4, Small: 3 (BigToSmall)
dieHard :: IO ()
dieHard = display =<< bmcCover Nothing True (pure ()) initial trans goal
  where -- we start from empty jugs, and try to reach a state where big has 4 gallons
        initial State{big, small, action} = (big, small, action) .== (0, 0, sInitial)
        goal    State{big}                = big .== 4

        -- Valid actions as a transition relation:
        trans :: SState -> SState -> SBool
        trans fromState toState = go actions
          where go []                = sFalse
                go ((act, f) : rest) = ite (toState.action .== act) (f fromState `matches` toState) (go rest)

                matches :: SState -> SState -> SBool
                p `matches` q = p.big .== q.big .&& p.small .== q.small

                infix 1 |=>
                a |=> f = (a, f)

                actions = [ sFillBig    |=> \st -> st{big   = 5}
                          , sFillSmall  |=> \st -> st{small = 3}

                          , sEmptyBig   |=> \st -> st{big   = 0}
                          , sEmptySmall |=> \st -> st{small = 0}

                          , sBigToSmall |=> \st -> let space = 3 - st.small
                                                       xfer  = space `smin` st.big
                                                   in st{big = st.big - xfer, small = st.small + xfer}

                          , sSmallToBig |=> \st -> let space = 5 - st.big
                                                       xfer  = space `smin` st.small
                                                   in st{big = st.big + xfer, small = st.small - xfer}
                          ]

        display :: Either String (Int, [State Integer Action]) -> IO ()
        display (Left e)        = error e
        display (Right (_, as)) = mapM_ print as
