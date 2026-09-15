-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.Arena
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Shared emission of per-call storage arenas for text and collections.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.Arena (CArena(..), arenaRuntime) where

-- | Separate ownership domains sharing the same allocation protocol. Keep
-- their C types and lifetimes independent even though their emitter is shared.
data CArena = TextArena  -- ^ Byte-addressed UTF-8 string storage.
            | ListArena -- ^ Aligned storage for symbolic-list elements.
            | SetArena  -- ^ Aligned storage for symbolic-set elements.

-- | Emit overflow-checked allocation and whole-arena cleanup. Empty allocations
-- return null without allocating. Collection storage retains its long-double
-- alignment and checks both multiplication and header-addition overflow; text
-- storage accepts a byte count directly. Nodes own only their payload buffer,
-- not the managed values referenced by collection elements.
arenaRuntime :: CArena -> [String]
arenaRuntime arena
  = [ "/* Per-call ownership arena for " ++ description ++ " temporaries. */"
    , "typedef struct " ++ nodeType ++ " { struct " ++ nodeType ++ " *next; " ++ payloadType ++ " data[]; } " ++ nodeType ++ ";"
    , "typedef struct { " ++ nodeType ++ " *head; } " ++ contextType ++ ";"
    ]
 ++ separator
 ++ [ "static " ++ resultType ++ " *" ++ prefix ++ "_alloc(" ++ contextType ++ " *ctx, size_t count" ++ elementParameter ++ ")"
    , "{"
    , "  if (count == 0) return NULL;"
    ]
 ++ [ line
    | not byteStorage
    , line <- [ "  if (element_size == 0 || count > SIZE_MAX / element_size) abort();"
              , "  const size_t bytes = count * element_size;"
              ]
    ]
 ++ [ "  if (" ++ byteCount ++ " > SIZE_MAX - sizeof(" ++ nodeType ++ ")) abort();"
    , "  " ++ nodeType ++ " *node = (" ++ nodeType ++ " *) malloc(sizeof(*node) + " ++ byteCount ++ ");"
    , "  if (node == NULL) abort();"
    , "  node->next = ctx->head; ctx->head = node; return node->data;"
    , "}"
    ]
 ++ separator
 ++ [ "static void " ++ prefix ++ "_ctx_end(" ++ contextType ++ " *ctx)"
    , "{"
    , "  while (ctx->head != NULL) {"
    , "    " ++ nodeType ++ " *next = ctx->head->next; free(ctx->head); ctx->head = next;"
    , "  }"
    , "}"
    ]
 where stem = case arena of
                TextArena -> "text"
                ListArena -> "list"
                SetArena  -> "set"
       description = case arena of
                       TextArena -> "string"
                       ListArena -> "symbolic-list"
                       SetArena  -> "symbolic-set"
       byteStorage = case arena of
                       TextArena -> True
                       _         -> False
       prefix           = "sbv_" ++ stem
       nodeType         = prefix ++ "_node"
       contextType      = prefix ++ "_ctx"
       payloadType      = if byteStorage then "uint8_t" else "long double"
       resultType       = if byteStorage then "uint8_t" else "void"
       byteCount        = if byteStorage then "count"   else "bytes"
       elementParameter = if byteStorage then ""        else ", size_t element_size"
       separator        = ["" | byteStorage]
