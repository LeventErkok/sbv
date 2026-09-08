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
  , arrayTypeDecls
  , arrayRuntime
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

-- | Emit opaque public array types for every kind used by a generated
-- program. Array values are borrowed references whose nodes live for the
-- duration of the generated function call.
arrayTypeDecls :: [Kind] -> Doc
arrayTypeDecls [] = empty
arrayTypeDecls kinds = text . unlines $
     ["/* Persistent functional arrays. References are valid for one generated call. */"
     , "#ifndef SBV_CGEN_UNUSED"
     , "#if defined(__GNUC__) || defined(__clang__)"
     , "#define SBV_CGEN_UNUSED __attribute__((unused))"
     , "#else"
     , "#define SBV_CGEN_UNUSED"
     , "#endif"
     , "#endif"]
  ++ concatMap declaration kinds
 where declaration kind = [ "#ifndef " ++ arrayGuard kind
                          , "#define " ++ arrayGuard kind
                          , "typedef struct " ++ arrayNodeType kind ++ " " ++ arrayNodeType kind ++ ";"
                          , "typedef const " ++ arrayNodeType kind ++ " *" ++ arrayCType kind ++ ";"
                          , "#endif"
                          , ""
                          ]

-- | Emit the node layouts and newest-write-first lookup helpers for every
-- array kind used by a generated program.
arrayRuntime :: CgConfig -> [Kind] -> Doc
arrayRuntime _   []    = empty
arrayRuntime cfg kinds = text . unlines $ "/* Persistent functional-array runtime. */" : concatMap runtime kinds
 where runtime kind@(KArray keyKind valueKind) =
         let nodeType    = arrayNodeType kind
             arrayType   = arrayCType kind
             keyType     = scalarCType keyKind
             valueType   = scalarCType valueKind
             readName    = arrayReadName kind
             keyEquality = P.render $ keyEqual cfg keyKind (text "array->key") (text "key")
         in [ "struct " ++ nodeType ++ " {"
            , "  bool is_store;"
            , "  " ++ arrayType ++ " parent;"
            , "  " ++ keyType ++ " key;"
            , "  " ++ valueType ++ " value;"
            , "};"
            , ""
            , "static SBV_CGEN_UNUSED " ++ valueType ++ " " ++ readName ++ "(" ++ arrayType ++ " array, " ++ keyType ++ " key)"
            , "{"
            , "  while (array->is_store) {"
            , "    if (" ++ keyEquality ++ ") return array->value;"
            , "    array = array->parent;"
            , "  }"
            , "  return array->value;"
            , "}"
            , ""
            ]
       runtime kind = error $ "SBV->C: Expected an array kind, received " ++ show kind

-- | Render a concrete array model as a nested chain of C99 compound literals.
-- Association-list entries retain SBV's newest-write-first ordering.
arrayConst :: (CV -> Doc) -> CV -> Maybe Doc
arrayConst renderValue (CV kind@(KArray keyKind valueKind) (CArray (ArrayModel associations defaultValue)))
  = Just $ foldr store base associations
 where base = nodeLiteral [text ".is_store = false", text ".value =" <+> renderValue (CV valueKind defaultValue)]

       store (key, value) parent = nodeLiteral
         [ text ".is_store = true"
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
             [text ".is_store = false", text ".value =" <+> defaultValue]
      (ArrayInit Right{}, [], [])
        -> unsupported "lambda-backed and free arrays"
      (ReadArray, [array, key], [renderedArray, renderedKey])
        | kindOf array == KArray (kindOf key) resultKind
        -> expression $ namedCall (arrayReadName (kindOf array)) [renderedArray, renderedKey]
      (WriteArray, [array, key, value], [renderedArray, renderedKey, renderedValue])
        | resultKind == kindOf array
        , resultKind == KArray (kindOf key) (kindOf value)
        -> nodeLowering resultKind
             [ text ".is_store = true"
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
arrayNodeType kind = "sbv_array_node_" ++ drop (length ("SBVArray_" :: String)) (arrayCType kind)

-- | Return the lookup-helper name for an array kind.
arrayReadName :: Kind -> String
arrayReadName kind = "sbv_array_read_" ++ drop (length ("SBVArray_" :: String)) (arrayCType kind)

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
