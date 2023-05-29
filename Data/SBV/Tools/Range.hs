-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.Range
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Single variable valid range detection.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.Range (

         -- * Boundaries and ranges
         Boundary(..), Range(..)

         -- * Computing valid ranges
       , ranges, rangesWith

       ) where

import Data.SBV
import Data.SBV.Control

import Data.SBV.Internals hiding (Range, free_)

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV
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
-- number of ranges is large, this can take a long time!
--
-- Beware that, as of June 2021, z3 no longer supports optimization with 'SReal' in the presence of
-- strict inequalities. See <https://github.com/Z3Prover/z3/issues/5314> for details. So, if you
-- have 'SReal' variables, it is important that you do /not/ use a strict inequality, i.e., '.>', '.<', './=' etc.
-- Inequalities of the form '.<=', '.>=' should be OK. Please report if you see any fishy
-- behavior due to this change in z3's behavior.
--
-- Some examples:
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
-- >>> ranges (\(x :: SReal) -> sAnd [x .>= 3.2, x .<= 12.7])
-- [[3.2,12.7]]
-- >>> ranges (\(x :: SReal) -> sAnd [x .<= 12.7, x ./= 8])
-- [(-oo,8.0),(8.0,12.7]]
-- >>> ranges (\(x :: SReal) -> sAnd [x .>= 12.7, x ./= 15])
-- [[12.7,15.0),(15.0,oo)]
-- >>> ranges (\(x :: SInt8) -> sAnd [x .<= 7, x ./= 6])
-- [[-128,6),(6,7]]
-- >>> ranges $ \x -> x .>= (0::SReal)
-- [[0.0,oo)]
-- >>> ranges $ \x -> x .<= (0::SReal)
-- [(-oo,0.0]]
-- >>> ranges $ \(x :: SWord8) -> 2*x .== 4
-- [[2,3),(129,130]]
ranges :: forall a. (Ord a, Num a, SymVal a,  SatModel a, Metric a, SymVal (MetricSpace a), SatModel (MetricSpace a)) => (SBV a -> SBool) -> IO [Range a]
ranges = rangesWith defaultSMTCfg

-- | Compute ranges, using the given solver configuration.
rangesWith :: forall a. (Ord a, Num a, SymVal a,  SatModel a, Metric a, SymVal (MetricSpace a), SatModel (MetricSpace a)) => SMTConfig -> (SBV a -> SBool) -> IO [Range a]
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
                                 Just (v :: MetricSpace a, []) -> case unliteral (fromMetricSpace (literal v)) of
                                                                    Nothing -> error $ "Data.SBV.ranges.getRegVal: Cannot extract value from metric space equivalent: " ++ show cv
                                                                    Just r  -> r
                                 _                             -> error $ "Data.SBV.ranges.getRegVal: Cannot parse " ++ show cv


                getBound cstr = do let objName = "boundValue"
                                   res@(LexicographicResult m) <- optimizeWith cfg Lexicographic $ do x <- free_
                                                                                                      constrain $ prop x
                                                                                                      cstr objName x
                                   case m of
                                     Unsatisfiable{} -> return Nothing
                                     Unknown{}       -> error "Solver said Unknown!"
                                     ProofError{}    -> error (show res)
                                     _               -> return $ getModelObjectiveValue objName m

            mi <- getBound minimize
            ma <- getBound maximize
            case (mi, ma) of
              (Just minV, Just maxV) -> return $ Just $ Range (getGenVal minV) (getGenVal maxV)
              _                      -> return Nothing

        -- Is this range satisfiable? Returns a witness to it.
        witness :: Range a -> Symbolic (SBV a)
        witness (Range lo hi) = do x :: SBV a <- free_

                                   let restrict v open closed = case v of
                                                                  Unbounded -> sTrue
                                                                  Open   a  -> x `open`   literal a
                                                                  Closed a  -> x `closed` literal a

                                       lower = restrict lo (.>) (.>=)
                                       upper = restrict hi (.<) (.<=)

                                   constrain $ lower .&& upper

                                   return x

        isFeasible :: Range a -> IO Bool
        isFeasible r = runSMTWith cfg $ do _ <- witness r

                                           query $ do cs <- checkSat
                                                      case cs of
                                                        Unsat  -> return False
                                                        DSat{} -> error "Data.SBV.interval.isFeasible: Solver returned a delta-satisfiable result!"
                                                        Unk    -> error "Data.SBV.interval.isFeasible: Solver said unknown!"
                                                        Sat    -> return True

        bisect :: Range a -> IO (Maybe [Range a])
        bisect r@(Range lo hi) = runSMTWith cfg $ do x <- witness r

                                                     constrain $ sNot (prop x)

                                                     query $ do cs <- checkSat
                                                                case cs of
                                                                  Unsat  -> return Nothing
                                                                  DSat{} -> error "Data.SBV.interval.bisect: Solver returned a delta-satisfiable result!"
                                                                  Unk    -> error "Data.SBV.interval.bisect: Solver said unknown!"
                                                                  Sat    -> do midV <- Open <$> getValue x
                                                                               return $ Just [Range lo midV, Range midV hi]

        search :: [Range a] -> [Range a] -> IO [Range a]
        search []     sofar = return $ reverse sofar
        search (c:cs) sofar = do feasible <- isFeasible c
                                 if feasible
                                    then do mbCS <- bisect c
                                            case mbCS of
                                              Nothing  -> search cs          (c:sofar)
                                              Just xss -> search (xss ++ cs) sofar
                                    else search cs sofar

{- HLint ignore rangesWith "Use fromMaybe" -}
