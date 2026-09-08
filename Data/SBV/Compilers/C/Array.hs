-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.Array
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Persistent functional-array lowering for the SBV-to-C compiler.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.Array
  ( arrayKinds
  , arrayCType
  , arrayInputCType
  , arrayTypeDecls
  , arrayRuntime
  , arrayInputSetup
  , arrayDriverCallback
  , arrayDriverInput
  , arrayConst
  , arrayExpr
  ) where

import Data.Char                        (isAsciiLower, toUpper)
import qualified Data.Set as Set

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>), render)

import Data.SBV.Compilers.C.BV         (isWideBV, wideBVEqual)
import Data.SBV.Compilers.C.FP         (arbitraryFPCType, arbitraryFPObjectEqual)
import Data.SBV.Compilers.C.GMP        (isExactGMPKind)
import Data.SBV.Compilers.C.Lowering   (CLowering(..), CRequirement(..), CStorage(..), expressionLowering)
import Data.SBV.Compilers.CodeGen      (CgConfig)
import Data.SBV.Core.Data

-- | Return and validate the distinct array kinds used by a program. This
-- first implementation deliberately excludes nested arrays; their value
-- ownership needs an explicit public lifetime policy.
arrayKinds :: Set.Set Kind -> [Kind]
arrayKinds = map validate . filter isArray . Set.toAscList
 where validate k@(KArray keyKind valueKind)
         | isArray keyKind || isArray valueKind
         = error $ "SBV->C: Nested arrays are not yet supported: " ++ show k
         | supported keyKind && supported valueKind
         = k
         | True
         = error $ "SBV->C: Array kind is not yet supported: " ++ show k
       validate kind = error $ "SBV->C: Expected an array kind, received " ++ show kind

       supported kind = case kind of
         KBool       -> True
         KBounded{}  -> True
         KUnbounded  -> True
         KReal       -> True
         KFloat      -> True
         KDouble     -> True
         KFP{}       -> True
         KADT{}      -> isRoundingMode kind
         _           -> False

-- | Return the public opaque-pointer type used for an SBV array kind.
arrayCType :: Kind -> String
arrayCType (KArray keyKind valueKind) = "SBVArray_" ++ kindTag keyKind ++ "_" ++ kindTag valueKind
arrayCType kind = error $ "SBV->C: Expected an array kind, received " ++ show kind

-- | Return the public callback-descriptor type accepted for an array-valued
-- C input. The descriptor and its context are borrowed for the duration of
-- the generated call.
arrayInputCType :: Kind -> String
arrayInputCType kind = "SBVArrayInput_" ++ arraySuffix kind

-- | Emit opaque public array types for every kind used by a generated
-- program. Array values are borrowed references whose nodes live for the
-- duration of the generated function call.
arrayTypeDecls :: [Kind] -> Doc
arrayTypeDecls [] = empty
arrayTypeDecls kinds = text . unlines $
     [ "/* Persistent functional arrays. References are valid for one generated call. */"
     , "/* Input callbacks and contexts are borrowed for that call; pointer-backed */"
     , "/* exact results returned by a callback must remain valid for the same period. */"
     , "#ifndef SBV_CGEN_UNUSED"
     , "#if defined(__GNUC__) || defined(__clang__)"
     , "#define SBV_CGEN_UNUSED __attribute__((unused))"
     , "#else"
     , "#define SBV_CGEN_UNUSED"
     , "#endif"
     , "#endif"]
  ++ concatMap declaration kinds
 where declaration kind@(KArray keyKind valueKind)
         = [ "#ifndef " ++ arrayGuard kind
           , "#define " ++ arrayGuard kind
           , "typedef struct " ++ arrayNodeType kind ++ " " ++ arrayNodeType kind ++ ";"
           , "typedef const " ++ arrayNodeType kind ++ " *" ++ arrayCType kind ++ ";"
           , "typedef " ++ scalarCType valueKind ++ " (*" ++ arrayLookupType kind ++ ")(const void *context, " ++ scalarCType keyKind ++ " key);"
           , "typedef struct { " ++ arrayLookupType kind ++ " lookup; const void *context; } " ++ arrayInputCType kind ++ ";"
           , "#endif"
           , ""
           ]
       declaration kind = error $ "SBV->C: Expected an array kind, received " ++ show kind

-- | Emit the node layouts and newest-write-first lookup helpers for every
-- array kind used by a generated program.
arrayRuntime :: CgConfig -> [Kind] -> Doc
arrayRuntime _   []    = empty
arrayRuntime cfg kinds = text . unlines $
     [ "/* Persistent functional-array runtime. */"
     , "typedef enum { SBV_ARRAY_CONSTANT, SBV_ARRAY_STORE, SBV_ARRAY_CALLBACK } SBVArrayNodeKind;"
     , ""
     ]
  ++ concatMap runtime kinds
 where runtime kind@(KArray keyKind valueKind) =
         let nodeType    = arrayNodeType kind
             arrayType   = arrayCType kind
             keyType     = scalarCType keyKind
             valueType   = scalarCType valueKind
             readName    = arrayReadName kind
             keyEquality = P.render $ keyEqual cfg keyKind (text "array->key") (text "key")
         in [ "struct " ++ nodeType ++ " {"
            , "  SBVArrayNodeKind kind;"
            , "  " ++ arrayType ++ " parent;"
            , "  " ++ keyType ++ " key;"
            , "  " ++ valueType ++ " value;"
            , "  " ++ arrayLookupType kind ++ " lookup;"
            , "  const void *context;"
            , "};"
            , ""
            , "static SBV_CGEN_UNUSED " ++ valueType ++ " " ++ readName ++ "(" ++ arrayType ++ " array, " ++ keyType ++ " key)"
            , "{"
            , "  while (array->kind == SBV_ARRAY_STORE) {"
            , "    if (" ++ keyEquality ++ ") return array->value;"
            , "    array = array->parent;"
            , "  }"
            , "  if (array->kind == SBV_ARRAY_CALLBACK) return array->lookup(array->context, key);"
            , "  return array->value;"
            , "}"
            , ""
            ]
       runtime kind = error $ "SBV->C: Expected an array kind, received " ++ show kind

-- | Materialize a borrowed public callback descriptor as an internal array
-- root. A null lookup callback is rejected before the symbolic program runs.
arrayInputSetup :: Int -> SV -> String -> [Doc]
arrayInputSetup typeWidth sv externalName
  | kind@KArray{} <- kindOf sv
  = [ text "if" P.<> parens (external P.<> text ".lookup == NULL") <+> text "abort" P.<> parens empty P.<> semi
    , text "const" <+> text (arrayNodeType kind) <+> text nodeName <+> text "=" <+> braces (fsep (punctuate comma fields)) P.<> semi
    , text "const" <+> paddedType <+> text (show sv) <+> text "=" <+> text "&" P.<> text nodeName P.<> semi
    ]
 where external   = text externalName
       nodeName   = "__sbv_array_input_" ++ show sv
       paddedType = text $ arrayCType (kindOf sv) ++ replicate (typeWidth - length (arrayCType (kindOf sv))) ' '
       fields     = [ text ".kind = SBV_ARRAY_CALLBACK"
                    , text ".lookup ="  <+> external P.<> text ".lookup"
                    , text ".context =" <+> external P.<> text ".context"
                    ]
arrayInputSetup _ sv _ = error $ "SBV->C: Expected an array input, received " ++ show (kindOf sv)

-- | Emit the default-only callback used by an example driver for an
-- array-valued input. The generated body illustrates the borrowed-context
-- protocol without pretending that a finite C object represents a total map.
arrayDriverCallback :: CgConfig -> Kind -> String -> String -> Doc
arrayDriverCallback cfg (KArray keyKind valueKind) functionName inputName
  = text "static" <+> text (scalarCType valueKind) <+> text callbackName
      P.<> parens (fsep (punctuate comma [text "const void *context", text (scalarCType keyKind) <+> text "key"]))
      $$ text "{"
      $$ nest 2 (   parens (text "void") <+> text "key" P.<> semi
                 $$ text "return" <+> result P.<> semi
                )
      $$ text "}"
 where callbackName = arrayDriverCallbackName functionName inputName
       result
         | isExactGMPKind cfg valueKind = parens (text (scalarCType valueKind)) <+> text "context"
         | True                          = text "*" P.<> parens (parens (text "const" <+> text (scalarCType valueKind) <+> text "*") <+> text "context")
arrayDriverCallback _ kind _ _ = error $ "SBV->C: Expected an array input kind, received " ++ show kind

-- | Construct an example-driver descriptor around a named default value and
-- its generated callback. Exact GMP defaults already decay to pointers;
-- ordinary values are passed to the callback by address.
arrayDriverInput :: CgConfig -> Kind -> String -> String -> String -> Doc
arrayDriverInput cfg kind functionName inputName defaultName
  | KArray _ valueKind <- kind
  = let context
          | isExactGMPKind cfg valueKind = text defaultName
          | True                          = text "&" P.<> text defaultName
    in text "const" <+> text (arrayInputCType kind) <+> text inputName <+> text "="
         <+> braces (fsep (punctuate comma [ text ".lookup ="  <+> text (arrayDriverCallbackName functionName inputName)
                                          , text ".context =" <+> context
                                          ])) P.<> semi
  | True
  = error $ "SBV->C: Expected an array input kind, received " ++ show kind

-- | Render a concrete array model as a nested chain of C99 compound literals.
-- Association-list entries retain SBV's newest-write-first ordering.
arrayConst :: (CV -> Doc) -> CV -> Maybe Doc
arrayConst renderValue (CV kind@(KArray keyKind valueKind) (CArray (ArrayModel associations defaultValue)))
  = Just $ foldr store base associations
 where base = nodeLiteral [text ".kind = SBV_ARRAY_CONSTANT", text ".value =" <+> renderValue (CV valueKind defaultValue)]

       store (key, value) parent = nodeLiteral
         [ text ".kind = SBV_ARRAY_STORE"
         , text ".parent =" <+> parent
         , text ".key ="    <+> renderValue (CV keyKind key)
         , text ".value ="  <+> renderValue (CV valueKind value)
         ]

       nodeLiteral fields = parens $ text "&" P.<> parens (text (arrayNodeType kind)) P.<> braces (fsep (punctuate comma fields))
arrayConst _ _ = Nothing

-- | Lower array initialization, reads, writes, and array-valued conditionals.
-- Lambda-backed and free arrays, nested arrays, and general extensional array
-- equality are rejected with focused diagnostics.
arrayExpr :: CgConfig -> Op -> [SV] -> SV -> [Doc] -> Maybe CLowering
arrayExpr cfg op svs resultSV args
  | not (isArray resultKind || any isArray svs)
  = Nothing
  | True
  = case (op, svs, args) of
      (ArrayInit (Left pair), [_], [defaultValue])
        | resultKind == uncurry KArray pair
        -> nodeLowering resultKind
             [text ".kind = SBV_ARRAY_CONSTANT", text ".value =" <+> defaultValue]
      (ArrayInit Right{}, [], [])
        -> unsupported "lambda-backed and free arrays"
      (ReadArray, [array, key], [renderedArray, renderedKey])
        | kindOf array == KArray (kindOf key) resultKind
        -> expression $ namedCall (arrayReadName (kindOf array)) [renderedArray, renderedKey]
      (WriteArray, [array, key, value], [renderedArray, renderedKey, renderedValue])
        | resultKind == kindOf array
        , resultKind == KArray (kindOf key) (kindOf value)
        -> nodeLowering resultKind
             [ text ".kind = SBV_ARRAY_STORE"
             , text ".parent =" <+> renderedArray
             , text ".key ="    <+> renderedKey
             , text ".value ="  <+> renderedValue
             ]
      (Ite, [_condition, left, right], [renderedCondition, renderedLeft, renderedRight])
        | resultKind == kindOf left
        , resultKind == kindOf right
        -> expression $ renderedCondition <+> text "?" <+> renderedLeft <+> text ":" <+> renderedRight
      (Label label, [_], [array])
        -> expression $ array <+> text "/*" <+> text label <+> text "*/"
      (Equal{}, _, _)    -> unsupported "general extensional array equality"
      (NotEqual, _, _)   -> unsupported "general extensional array equality"
      _                  -> error $ "SBV->C: Unsupported array operation " ++ show op
                           ++ " with argument kinds " ++ show (map kindOf svs)
                           ++ " and result kind " ++ show resultKind
 where resultKind = kindOf resultSV

       expression = Just . expressionLowering storage requirements

       storage
         | isExactGMPKind cfg resultKind = CFunctionScoped
         | isArray resultKind            = CFunctionScoped
         | True                          = CByValue

       nodeLowering kind fields = Just CLowering
         { loweringExpression   = text "&" P.<> text nodeName
         , loweringSetup        = [text "const" <+> text (arrayNodeType kind) <+> text nodeName <+> text "=" <+> braces (fsep (punctuate comma fields)) P.<> semi]
         , loweringCleanup      = []
         , loweringRequirements = Set.fromList requirements
         , loweringStorage      = CFunctionScoped
         }

       nodeName = "__sbv_array_" ++ show resultSV

       requirements = CRequiresArrays : concatMap kindRequirements (resultKind : map kindOf svs)

       kindRequirements kind
         | isWideBV kind                 = [CRequiresWideBV]
         | isFP kind                     = [CRequiresLibBF, CRequiresLibM]
         | isExactGMPKind cfg kind        = [CRequiresGMP]
         | kind `elem` [KFloat, KDouble] = [CRequiresLibM]
         | KArray keyKind valueKind <- kind
         = kindRequirements keyKind ++ kindRequirements valueKind
         | True = []

       unsupported feature = error $ "SBV->C: Arrays do not yet support " ++ feature ++ "."

       namedCall functionName callArgs = text functionName P.<> parens (fsep (punctuate comma callArgs))

-- | Return the concrete node-structure name for an array kind.
arrayNodeType :: Kind -> String
arrayNodeType kind = "sbv_array_node_" ++ arraySuffix kind

-- | Return the lookup-helper name for an array kind.
arrayReadName :: Kind -> String
arrayReadName kind = "sbv_array_read_" ++ arraySuffix kind

-- | Return the callback-function-pointer type for an array kind.
arrayLookupType :: Kind -> String
arrayLookupType kind = "SBVArrayLookup_" ++ arraySuffix kind

-- | Return the generated example-driver callback name for an input.
arrayDriverCallbackName :: String -> String -> String
arrayDriverCallbackName functionName inputName = "__sbv_array_lookup_f" ++ tagged functionName ++ "_i" ++ tagged inputName
 where tagged identifier = show (length identifier) ++ "_" ++ identifier

-- | Return the key/value suffix shared by the generated names for an array
-- kind.
arraySuffix :: Kind -> String
arraySuffix (KArray keyKind valueKind) = kindTag keyKind ++ "_" ++ kindTag valueKind
arraySuffix kind = error $ "SBV->C: Expected an array kind, received " ++ show kind

-- | Return the preprocessor guard protecting an array type declaration.
arrayGuard :: Kind -> String
arrayGuard kind = map guardChar (arrayCType kind) ++ "_DEFINED"
 where guardChar c
         | isAsciiLower c = toUpper c
         | True           = c

-- | Return the compact identifier fragment used for one supported scalar
-- kind in generated array symbols.
kindTag :: Kind -> String
kindTag KBool              = "u1"
kindTag (KBounded False w) = "u" ++ show w
kindTag (KBounded True  w) = "s" ++ show w
kindTag KUnbounded         = "integer"
kindTag KReal              = "real"
kindTag KFloat             = "float"
kindTag KDouble            = "double"
kindTag (KFP eb sb)        = "fp_e" ++ show eb ++ "_s" ++ show sb
kindTag kind
  | isRoundingMode kind = "rounding_mode"
  | True                = error $ "SBV->C: Unsupported scalar array kind: " ++ show kind

-- | Return the public C spelling for a scalar kind stored in an array node.
scalarCType :: Kind -> String
scalarCType KBool               = "SBool"
scalarCType (KBounded False 1)  = "SBool"
scalarCType (KBounded False w)  = "SWord" ++ show w
scalarCType (KBounded True  w)  = "SInt" ++ show w
scalarCType KUnbounded          = "SInteger"
scalarCType KReal               = "SReal"
scalarCType KFloat              = "SFloat"
scalarCType KDouble             = "SDouble"
scalarCType kind@KFP{}          = arbitraryFPCType kind
scalarCType kind
  | isRoundingMode kind = "RoundingMode"
  | True                = error $ "SBV->C: Unsupported scalar array kind: " ++ show kind

-- | Render the strong equality used to match array keys. Unlike IEEE numeric
-- equality, this comparison identifies NaNs and distinguishes signed zeroes.
keyEqual :: CgConfig -> Kind -> Doc -> Doc -> Doc
keyEqual cfg kind left right
  | isWideBV kind           = wideBVEqual kind left right
  | isExactGMPKind cfg kind = parens $ namedCall comparison [left, right] <+> text "== 0"
  | isFP kind               = arbitraryFPObjectEqual kind left right
  | kind `elem` [KFloat, KDouble]
  = parens $    parens (namedCall "isnan" [left] <+> text "&&" <+> namedCall "isnan" [right])
            <+> text "||"
            <+> parens (   left <+> text "==" <+> right
                       <+> text "&&"
                       <+> parens (   left <+> text "!= 0"
                                  <+> text "||"
                                  <+> namedCall "signbit" [left] <+> text "==" <+> namedCall "signbit" [right]
                                 )
                      )
  | True = parens $ left <+> text "==" <+> right
 where comparison
         | kind == KUnbounded = "mpz_cmp"
         | kind == KReal      = "mpq_cmp"
         | True               = error $ "SBV->C: Expected an exact GMP array key, received " ++ show kind

       namedCall functionName callArgs = text functionName P.<> parens (fsep (punctuate comma callArgs))
