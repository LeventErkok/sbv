-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.Range
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Single variable valid range detection.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Tools.Range (

         -- * Boundaries and ranges
         Boundary(..), Range(..)

         -- * Computing valid ranges
       , ranges, rangesWith

       ) where

import Data.SBV
import Data.SBV.Control

import Data.SBV.Internals hiding (Range, free_)

-- Doctest only
-- $setup
-- >>> :set -XScopedTypeVariables

-- | A boundary value
data Boundary a = Unbounded -- ^ Unbounded
                | Open   a  -- ^ Exclusive of the point
                | Closed a  -- ^ Inclusive of the point

-- | Is this a closed value?
isClosed :: Boundary a -> Bool
isClosed Unbounded  = False
isClosed (Open   _) = False
isClosed (Closed _) = True

-- | A range is a pair of boundaries: Lower and upper bounds
data Range a = Range (Boundary a) (Boundary a)

-- | Show instance for 'Range'
instance Show a => Show (Range a) where
   show (Range l u) = sh True l ++ "," ++ sh False u
     where sh onLeft b = case b of
                           Unbounded | onLeft -> "(-oo"
                                     | True   -> "oo)"
                           Open   v  | onLeft -> "(" ++ show v
                                     | True   -> show v ++ ")"
                           Closed v  | onLeft -> "[" ++ show v
                                     | True   -> show v ++ "]"

-- | Given a single predicate over a single variable, find the contiguous ranges over which the predicate
-- is satisfied. SBV will make one call to the optimizer, and then as many calls to the solver as there are
-- disjoint ranges that the predicate is satisfied over. (Linear in the number of ranges.) Note that the
-- number of ranges is large, this can take a long time! Some examples:
--
-- >>> ranges (\(_ :: SInteger) -> sFalse)
-- []
-- >>> ranges (\(_ :: SInteger) -> sTrue)
-- [(-oo,oo)]
-- >>> ranges (\(x :: SInteger) -> sAnd [x .<= 120, x .>= -12, x ./= 3])
-- [[-12,3),(3,120]]
-- >>> ranges (\(x :: SInteger) -> sAnd [x .<= 75, x .>= 5, x ./= 6, x ./= 67])
-- [[5,6),(6,67),(67,75]]
-- >>> ranges (\(x :: SInteger) -> sAnd [x .<= 75, x ./= 3, x ./= 67])
-- [(-oo,3),(3,67),(67,75]]
-- >>> ranges (\(x :: SReal) -> sAnd [x .> 3.2, x .<  12.7])
-- [(3.2,12.7)]
-- >>> ranges (\(x :: SReal) -> sAnd [x .> 3.2, x .<= 12.7])
-- [(3.2,12.7]]
-- >>> ranges (\(x :: SReal) -> sAnd [x .<= 12.7, x ./= 8])
-- [(-oo,8.0),(8.0,12.7]]
-- >>> ranges (\(x :: SReal) -> sAnd [x .>= 12.7, x ./= 15])
-- [[12.7,15.0),(15.0,oo)]
-- >>> ranges (\(x :: SInt8) -> sAnd [x .<= 7, x ./= 6])
-- [[-128,6),(6,7]]
-- >>> ranges $ \x -> x .> (0::SReal)
-- [(0.0,oo)]
-- >>> ranges $ \x -> x .< (0::SReal)
-- [(-oo,0.0)]
ranges :: forall a. (Num a, SymVal a,  SMTValue a, SatModel a, Metric (SBV a)) => (SBV a -> SBool) -> IO [Range a]
ranges = rangesWith defaultSMTCfg

-- | Compute ranges, using the given solver configuration.
rangesWith :: forall a. (Num a, SymVal a,  SMTValue a, SatModel a, Metric (SBV a)) => SMTConfig -> (SBV a -> SBool) -> IO [Range a]
rangesWith cfg prop = do mbBounds <- getInitialBounds
                         case mbBounds of
                           Nothing -> return []
                           Just r  -> search [r] []

  where getInitialBounds :: IO (Maybe (Range a))
        getInitialBounds = do
            let getGenVal :: GeneralizedCV -> Boundary a
                getGenVal (RegularCV  cv)  = Closed $ getRegVal cv
                getGenVal (ExtendedCV ecv) = getExtVal ecv

                getExtVal :: ExtCV -> Boundary a
                getExtVal (Infinite _) = Unbounded
                getExtVal (Epsilon  k) = Open $ getRegVal (mkConstCV k (0::Integer))
                getExtVal i@Interval{} = error $ unlines [ "*** Data.SBV.ranges.getExtVal: Unexpected interval bounds!"
                                                         , "***"
                                                         , "*** Found bound: " ++ show i
                                                         , "*** Please report this as a bug!"
                                                         ]
                getExtVal (BoundedCV cv) = Closed $ getRegVal cv
                getExtVal (AddExtCV a b) = getExtVal a `addBound` getExtVal b
                getExtVal (MulExtCV a b) = getExtVal a `mulBound` getExtVal b

                opBound :: (a -> a -> a) -> Boundary a -> Boundary a -> Boundary a
                opBound f x y = case (fromBound x, fromBound y, isClosed x && isClosed y) of
                                  (Just a, Just b, True)  -> Closed $ a `f` b
                                  (Just a, Just b, False) -> Open   $ a `f` b
                                  _                       -> Unbounded
                  where fromBound Unbounded  = Nothing
                        fromBound (Open   a) = Just a
                        fromBound (Closed a) = Just a

                addBound, mulBound :: Boundary a -> Boundary a -> Boundary a
                addBound = opBound (+)
                mulBound = opBound (*)

                getRegVal :: CV -> a
                getRegVal cv = case parseCVs [cv] of
                                 Just (v, []) -> v
                                 _            -> error $ "Data.SBV.interval.getRegVal: Cannot parse " ++ show cv

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
                                                                    Unbounded -> sTrue
                                                                    Open   a  -> x `open`   literal a
                                                                    Closed a  -> x `closed` literal a

                                         lower = restrict lo (.>) (.>=)
                                         upper = restrict hi (.<) (.<=)

                                     constrain $ lower .&& upper .&& sNot (prop x)

                                     query $ do cs <- checkSat
                                                case cs of
                                                  Unsat -> return Nothing
                                                  Unk   -> error "Data.SBV.interval.bisect: Solver said unknown!"
                                                  Sat   -> do midV <- Open <$> getValue x
                                                              return $ Just [Range lo midV, Range midV hi]

        search :: [Range a] -> [Range a] -> IO [Range a]
        search []     sofar = return $ reverse sofar
        search (c:cs) sofar = do mbCS <- bisect c
                                 case mbCS of
                                   Nothing  -> search cs          (c:sofar)
                                   Just xss -> search (xss ++ cs) sofar
