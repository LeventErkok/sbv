{-# LANGUAGE CPP #-}

-- | Compatibility shim for GHC 7.8 support. Remove once 7.8 is no
-- longer supported.

#if MIN_VERSION_base(4,8,0)

module GHC.Stack.Compat (module GHC.Stack) where
import GHC.Stack

#else

module GHC.Stack.Compat {-# WARNING "This version of GHC does not support SrcLoc; using a stub interface for compatibility" #-} (module GHC.Stack.Compat) where

import GHC.SrcLoc.Compat

data CallStack

getCallStack :: CallStack -> [(String, SrcLoc)]
getCallStack _ = []

showCallStack :: CallStack -> String
showCallStack _ = "CallStack not supported in GHC older than 7.10"

#endif
