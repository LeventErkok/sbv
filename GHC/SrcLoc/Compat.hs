{-# LANGUAGE CPP #-}

-- | Compatibility shims for the SrcLoc interface across GHC versions

module GHC.SrcLoc.Compat (module X) where

#if MIN_VERSION_base(4,9,0)
import SrcLoc as X hiding (srcLocFile)
#else
import GHC.SrcLoc as X
#endif
