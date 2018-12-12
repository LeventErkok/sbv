-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Tools.Range
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Single variable valid range detection.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Tools.Range(

        -- * Boundaries and ranges
        Range(..), Boundary(..)

        -- * Computing valid ranges
        , range
        ) where

import Data.SBV
import Data.SBV.Control

import Data.SBV.Internals hiding (Range)

data Boundary a = Open (Maybe a) | Closed (Maybe a)
data Range a    = Range (Boundary a) (Boundary a)

instance Show a => Show (Range a) where
   show (Range l u) = sh True l ++ "," ++ sh False u
     where sh onLeft b = case b of
                           Open  Nothing   | onLeft -> "(-oo"
                                           | True   -> "oo)"
                           Open  (Just v)  | onLeft -> "(" ++ show v
                                           | True   -> show v ++ ")"
                           Closed Nothing  | onLeft -> "[-oo"
                                           | True   -> "oo]"
                           Closed (Just v) | onLeft -> "[" ++ show v
                                           | True   -> show v ++ "]"

range :: forall a. (SymWord a,  SMTValue a, SatModel a, Metric (SBV a)) => (SBV a -> SBool) -> IO [Range a]
range prop = do mbBounds <- getInitialBounds
                case mbBounds of
                  Nothing -> return []
                  Just r  -> search [r] []

  where getInitialBounds :: IO (Maybe (Range a))
        getInitialBounds = do
            let getGenVal :: GeneralizedCW -> Boundary a
                getGenVal (ExtendedCW (Infinite _))                                       = Closed Nothing
                getGenVal (ExtendedCW (MulExtCW _ (Infinite _)))                          = Closed Nothing
                getGenVal (ExtendedCW (BoundedCW cw))                                     = Closed $ Just $ getRegVal cw
                getGenVal (RegularCW  cw)                                                 = Closed $ Just $ getRegVal cw
                getGenVal (ExtendedCW (AddExtCW (BoundedCW cw) (Epsilon _)))              = Open   $ Just $ getRegVal cw
                getGenVal (ExtendedCW (AddExtCW (BoundedCW cw) (MulExtCW _ (Epsilon _)))) = Open   $ Just $ getRegVal cw
                getGenVal gw                                                              = error $ "Data.SBV.interval.getGenVal: TBD: " ++ show gw

                getRegVal :: CW -> a
                getRegVal cw = case parseCWs [cw] of
                                 Just (v, []) -> v
                                 _            -> error $ "Data.SBV.interval.getRegVal: Cannot parse " ++ show cw

            IndependentResult m <- optimize Independent $ do x <- free_
                                                             constrain $ prop x
                                                             minimize "min" x
                                                             maximize "max" x
            case head (map snd m) of
              Unsatisfiable{} -> return Nothing
              Unknown{}       -> error "Solver said Unknown!"
              ProofError{}    -> error (show (IndependentResult m))
              _               -> let Just (Just mi) = getModelObjectiveValue "min" `fmap` ("min" `lookup` m)
                                     Just (Just ma) = getModelObjectiveValue "max" `fmap` ("max" `lookup` m)
                                 in return $ Just $ Range (getGenVal mi) (getGenVal ma)


        bisect :: Range a -> IO (Maybe [Range a])
        bisect (Range lo hi) = runSMT $ do x <- free_

                                           let lower = case lo of
                                                         Open  Nothing   -> true
                                                         Open  (Just v)  -> x .> literal v
                                                         Closed Nothing  -> true
                                                         Closed (Just v) -> x .>= literal v

                                               upper = case hi of
                                                         Open  Nothing   -> true
                                                         Open  (Just v)  -> x .< literal v
                                                         Closed Nothing  -> true
                                                         Closed (Just v) -> x .<= literal v

                                           constrain $ lower &&& upper &&& bnot (prop x)

                                           query $ do cs <- checkSat
                                                      case cs of
                                                        Unsat -> return Nothing
                                                        Unk   -> error "Data.SBV.interval.bisect: Solver said unknown!"
                                                        Sat   -> do midV <- Open . Just <$> getValue x
                                                                    return $ Just [Range lo midV, Range midV hi]

        search :: [Range a] -> [Range a] -> IO [Range a]
        search []     sofar = return $ reverse sofar
        search (c:cs) sofar = do mbCS <- bisect c
                                 case mbCS of
                                   Nothing  -> search cs          (c:sofar)
                                   Just xss -> search (xss ++ cs) sofar

{-
-- Prints:
-- [[-oo,oo]]
-- []
-- [[-12,3),(3,120]]
-- [[5,6),(6,67),(67,75]]
-- [[-oo,3),(3,67),(67,75]]
-- [(3.2,12.7)]
-- [(3.2,12.7]]
-- [[-oo,8.0),(8.0,12.7]]
-- [[-128,6),(6,7]]
main :: IO ()
main = do print =<< interval (\(_ :: SInteger) -> true)
          print =<< interval (\(_ :: SInteger) -> false)
          print =<< interval (\(x :: SInteger) -> bAnd [x .<= 120, x .>= -12, x ./= 3])
          print =<< interval (\(x :: SInteger) -> bAnd [x .<= 75, x .>= 5, x ./= 6, x ./= 67])
          print =<< interval (\(x :: SInteger) -> bAnd [x .<= 75, x ./= 3, x ./= 67])
          print =<< interval (\(x :: SReal)    -> bAnd [x .> 3.2, x .<  12.7])
          print =<< interval (\(x :: SReal)    -> bAnd [x .> 3.2, x .<= 12.7])
          print =<< interval (\(x :: SReal)    -> bAnd [x .<= 12.7, x ./= 8])
          print =<< interval (\(x :: SInt8)    -> bAnd [x .<= 7, x ./= 6])
-}
