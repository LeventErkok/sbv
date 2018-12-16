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

module Data.SBV.Tools.Range (

         -- * Boundaries and ranges
         Range(..), Boundary(..)

         -- * Computing valid ranges
       , ranges, rangesWith

       ) where

import Data.SBV
import Data.SBV.Control

import Data.SBV.Internals hiding (Range)

-- Doctest only
-- $setup
-- >>> :set -XScopedTypeVariables

-- | A boundary over an optional value. In 'Open', 'Nothing' signifies @Infinity@.
data Boundary a = Open   (Maybe a)   -- ^ Exclusive of the point
                | Closed a           -- ^ Inclusive of the point

-- | A range is a pair of boundaries: Lower and upper bounds
data Range a = Range (Boundary a) (Boundary a)

-- | Show instance for 'Range'
instance Show a => Show (Range a) where
   show (Range l u) = sh True l ++ "," ++ sh False u
     where sh onLeft b = case b of
                           Open   Nothing  | onLeft -> "(-oo"
                                           | True   -> "oo)"
                           Open   (Just v) | onLeft -> "(" ++ show v
                                           | True   -> show v ++ ")"
                           Closed v        | onLeft -> "[" ++ show v
                                           | True   -> show v ++ "]"

-- | Given a single predicate over a single variable, find the contiguous ranges over which the predicate
-- is satisfied. SBV will make one call to the optimizer, and then as many calls to the solver as there are
-- disjoint ranges that the predicate is satisfied over. (Linear in the number of ranges.) Note that the
-- number of ranges is large, this can take a long time! Some examples:
--
-- >>> ranges (\(_ :: SInteger) -> false)
-- []
-- >>> ranges (\(_ :: SInteger) -> true)
-- [(-oo,oo)]
-- >>> ranges (\(x :: SInteger) -> bAnd [x .<= 120, x .>= -12, x ./= 3])
-- [[-12,3),(3,120]]
-- >>> ranges (\(x :: SInteger) -> bAnd [x .<= 75, x .>= 5, x ./= 6, x ./= 67])
-- [[5,6),(6,67),(67,75]]
-- >>> ranges (\(x :: SInteger) -> bAnd [x .<= 75, x ./= 3, x ./= 67])
-- [(-oo,3),(3,67),(67,75]]
-- >>> ranges (\(x :: SReal) -> bAnd [x .> 3.2, x .<  12.7])
-- [(3.2,12.7)]
-- >>> ranges (\(x :: SReal) -> bAnd [x .> 3.2, x .<= 12.7])
-- [(3.2,12.7]]
-- >>> ranges (\(x :: SReal) -> bAnd [x .<= 12.7, x ./= 8])
-- [(-oo,8.0),(8.0,12.7]]
-- >>> ranges (\(x :: SReal) -> bAnd [x .>= 12.7, x ./= 15])
-- [[12.7,15.0),(15.0,oo)]
-- >>> ranges (\(x :: SInt8) -> bAnd [x .<= 7, x ./= 6])
-- [[-128,6),(6,7]]
-- >>> ranges $ \x -> x .> (0::SReal)
-- [(0.0,oo)]
-- >>> ranges $ \x -> x .< (0::SReal)
-- [(-oo,0.0)]
ranges :: forall a. (SymWord a,  SMTValue a, SatModel a, Metric (SBV a)) => (SBV a -> SBool) -> IO [Range a]
ranges = rangesWith defaultSMTCfg

-- | Compute ranges, using the given solver configuration
rangesWith :: forall a. (SymWord a,  SMTValue a, SatModel a, Metric (SBV a)) => SMTConfig -> (SBV a -> SBool) -> IO [Range a]
rangesWith cfg prop = do mbBounds <- getInitialBounds
                         case mbBounds of
                           Nothing -> return []
                           Just r  -> search [r] []

  where getInitialBounds :: IO (Maybe (Range a))
        getInitialBounds = do
            let getGenVal :: GeneralizedCW -> Boundary a
                getGenVal (ExtendedCW (BoundedCW cw))                                     = Closed $ getRegVal cw
                getGenVal (RegularCW  cw)                                                 = Closed $ getRegVal cw
                getGenVal (ExtendedCW (Infinite _))                                       = Open Nothing
                getGenVal (ExtendedCW (MulExtCW _ (Infinite _)))                          = Open Nothing
                getGenVal (ExtendedCW (Epsilon k))                                        = Open $ Just $ getRegVal (mkConstCW k (0::Integer))
                getGenVal (ExtendedCW (MulExtCW _ (Epsilon k)))                           = Open $ Just $ getRegVal (mkConstCW k (0::Integer))
                getGenVal (ExtendedCW (AddExtCW (BoundedCW cw) (Epsilon _)))              = Open $ Just $ getRegVal cw
                getGenVal (ExtendedCW (AddExtCW (BoundedCW cw) (MulExtCW _ (Epsilon _)))) = Open $ Just $ getRegVal cw
                getGenVal gw                                                              = error $ "Data.SBV.interval.getGenVal: TBD: " ++ show gw

                getRegVal :: CW -> a
                getRegVal cw = case parseCWs [cw] of
                                 Just (v, []) -> v
                                 _            -> error $ "Data.SBV.interval.getRegVal: Cannot parse " ++ show cw

            IndependentResult m <- optimizeWith cfg Independent $ do x <- free_
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
        bisect (Range lo hi) = runSMTWith cfg $ do
                                     x <- free_

                                     let restrict v open closed = case v of
                                                                    Open  Nothing  -> true
                                                                    Open  (Just a) -> x `open`   literal a
                                                                    Closed a       -> x `closed` literal a

                                         lower = restrict lo (.>) (.>=)
                                         upper = restrict hi (.<) (.<=)

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
