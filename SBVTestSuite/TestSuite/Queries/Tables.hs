-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.Tables
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test case for https://github.com/LeventErkok/sbv/issues/539
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass                #-}
{-# LANGUAGE DeriveGeneric                 #-}
{-# LANGUAGE FlexibleContexts              #-}
{-# LANGUAGE Rank2Types                    #-}
{-# LANGUAGE QuantifiedConstraints         #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-orphans #-}

module TestSuite.Queries.Tables (tests)  where

import GHC.Generics hiding (S)
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State

import qualified Data.SBV.Maybe as SBV
import qualified Data.SBV.Tuple as SBV

import Data.SBV.Control
import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Tables"
    [ goldenCapturedIO "queryTables" testTables
    ]

testTables :: FilePath -> IO ()
testTables rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} tables
                   appendFile rf ("\n FINAL:" ++ show r ++ "\nDONE!\n")

data S = S { currentRoom   :: SInt16
           , itemLocations :: [SInt16]
           } deriving (Show, Generic, Mergeable)

tables :: Symbolic [(Int16, Int16)]
tables = do
    let theGame = Game
            { gameDictSize = 1
            , gameItems = [7]
            , gameRooms = [[0],[2]]
            }


    let genWord = do
            word <- freshVar_
            constrain $ 0 .<= word .&& word .< literal (gameDictSize theGame)
            return word
        genCmd = do
            verb <- genWord
            noun <- genWord
            return $ SBV.tuple (verb, noun)
    query $ do
            let s0 = initState theGame

            let step cmd = do
                    let (verb, noun) = SBV.untuple cmd
                    runGame theGame $ stepPlayer (verb, noun)

            cmd1 <- genCmd
            push 1
            (f1, s1) <- return $ runState (step cmd1) s0
            constrain f1
            _cs <- checkSat
            pop 1

            cmd2 <- genCmd
            push 1
            (f2, _s2) <- return $ runState (step cmd2) s1
            constrain f2
            _cs <- checkSat

            mapM getValue [cmd1, cmd2]

instance forall a. Mergeable a => Mergeable (Identity a) where
    symbolicMerge force cond thn els = Identity $ symbolicMerge force cond (runIdentity thn) (runIdentity els)

instance (Mergeable a, forall b. Mergeable b => Mergeable (m b)) => Mergeable (ReaderT r m a) where
    symbolicMerge force cond thn els = ReaderT $ symbolicMerge force cond (runReaderT thn) (runReaderT els)

instance (Mergeable s, Mergeable a, forall b. Mergeable b => Mergeable (m b)) => Mergeable (StateT s m a) where
    symbolicMerge force cond thn els = StateT $ symbolicMerge force cond (runStateT thn) (runStateT els)

data Game = Game { gameDictSize :: Int16
                 , gameItems :: [Int16]
                 , gameRooms :: [[Int16]]
                 } deriving Show

type SInput = (SInt16, SInt16)

type Engine = ReaderT Game (State S)

carried :: Int16
carried = 255

initState :: Game -> S
initState _game = S { currentRoom = 0
                    , itemLocations = [1]
                    }

runGame :: Game -> Engine a -> State S a
runGame game act = runReaderT act game

stepPlayer :: SInput -> Engine SBool
stepPlayer (v, n) = do
    perform (v, n)
    finished

finished :: Engine SBool
finished = do
    locs <- gets itemLocations
    return $ map (.== 1) locs `pbExactly` 1

perform :: SInput -> Engine ()
perform (verb, noun) = sCase verb (return ())
    [ (1, builtin_go)
    , (10, builtin_get)
    ]
  where
    builtin_go = sWhen (1 .<= noun .&& noun .<= 6) $ do
        let dir = noun - 1
        here <- gets currentRoom
        exits <- asks $ (.!! here) . map (map literal) . gameRooms
        let newRoom = select exits 0 dir
        sUnless (newRoom .== 0) $ modify $ \s ->
          s{ currentRoom = newRoom }

    builtin_get = do
        locs <- gets itemLocations
        here <- gets currentRoom
        items <- asks gameItems
        let item = SBV.fromMaybe (-1) $ sFindIndex (\nm -> noun .== literal nm) items
        sWhen (select locs (-1) item .== here) $ modify $ \s ->
          s{ itemLocations = replaceAt item (literal carried) (itemLocations s) }

(.!!) :: (Mergeable a) => [a] -> SInt16 -> a
xs .!! i = case xs of
    [] -> error "(.!) : empty array"
    lst@(x:_) -> select lst x i

replaceAt :: (Mergeable a) => SInt16 -> a -> [a] -> [a]
replaceAt i x' = zipWith (\j x -> ite (i .== literal j) x' x) [0..]

sCase :: (Mergeable a) => SInt16 -> a -> [(Int16, a)] -> a
sCase x def = go
  where
    go [] = def
    go ((k,v):kvs) = ite (x .== literal k) v (go kvs)

sUnless :: (Monad m, Mergeable (m ())) => SBool -> m () -> m ()
sUnless b = ite b (return ())

sWhen :: (Monad m, Mergeable (m ())) => SBool -> m () -> m ()
sWhen b act = ite b act (return ())

sFindIndex :: (a -> SBool) -> [a] -> SMaybe Int16
sFindIndex p = go 0
  where
    go _ [] = SBV.sNothing
    go i (x:xs) = ite (p x) (SBV.sJust i) (go (i + 1) xs)
