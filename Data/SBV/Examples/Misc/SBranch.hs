-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Misc.SBranch
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Illustrates the use of 'sBranch', as a means of dealing with certain cases
-- of the symbolic-termination problem.
-----------------------------------------------------------------------------

module Data.SBV.Examples.Misc.SBranch where

import Data.SBV

-- | A fast implementation of population-count. Note that SBV already provides
-- this functionality via 'sbvPopCount', using simple expansion and counting
-- algorithm. 'sbvPopCount' is linear in the size of the input, i.e., a 32-bit
-- word would take 32 additions. This implementation here is /faster/ in the
-- sense that it takes as many additions as there are set-bits in the given word.
--
-- Of course, the issue is that this definition is recursive, and the usual
-- definition via 'ite' would never symbolically terminate: Recursion is done
-- on the input argument: In each recursive call, we /reduce/ the value @n@
-- to @n .&. (n-1)@. This eliminates one set-bit in the input. However, this
-- claim is far from obvious. By the use of 'sBranch' we tell SBV to call
-- the SMT solver in each test to ensure we only evaluate the branches we need,
-- thus avoiding the symbolic-termination issue. In a sense, the SMT solvers
-- proves that the implementation terminates for all valid inputs.
--
-- Note that replacing 'sBranch' in this implementation with 'ite' would cause
-- symbolic-termination to loop forever. Of course, this does /not/ mean that
-- 'sBranch' is fast: It is costly to make external calls to the solver for
-- each branch, so use with care.
bitCount :: SWord32 -> SWord8
bitCount = go 0
  where go c n = sBranch (n .== 0) c (go (c+1) (n .&. (n-1)))

-- | Prove that the 'bitCount' function implemented here is equivalent to
-- the internal "slower" implementation. We have:
--
-- >>> prop
-- Q.E.D.
prop :: IO ThmResult
prop = prove $ \n -> bitCount n .== sbvPopCount n

-- | Illustrates the use of path-conditions in avoiding infeasible paths in symbolic
-- simulation. If we used 'ite' instead of 'sBranch' in the else-branch of the
-- implementation of 'path' symbolic simulation would have encountered the 'error' call, and
-- hence would have failed. But 'sBranch' keeps track of the path condition, and can
-- successfully determine that this path will never be taken, and hence avoids the problem.
-- Note that we can freely mix/match 'ite' and 'sBranch' calls; path conditions will be
-- tracked in both cases. In fact, use of 'ite' is advisable if we know for a fact that
-- both branches are feasible, as it avoids the external call. 'sBranch' will have the
-- same result, albeit it'll cost more.
path :: SWord8 -> SWord8
path x = ite (x .> 5)
             10
             (sBranch (x .> 10)
                      (error "this case is not reachable!")  -- NB. x .> 5 fails, so can't be .> 10 here
                      20)

-- | Prove that 'path' always produces either @10@ or @20@, i.e., symbolic simulation will
-- not fail due to the 'error' call. We have:
--
-- >>> pathCheck
-- Q.E.D.
--
-- Were we to use 'ite' instead of 'sBranch' in the implementation of 'path', this expression
-- would have caused an exception to be raised at symbolic simulation time.
pathCheck :: IO ThmResult
pathCheck = prove $ \n -> let pn = path n in pn .== 10 ||| pn .== 20
