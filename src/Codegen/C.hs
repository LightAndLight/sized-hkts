{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
module Codegen.C
  ( Ann(..)
  , C(..)
  , CDecl(..)
  , CStatement(..)
  , CType(..)
  , CExpr(..)
  , preamble
  , render
  , prettyCDecls
  , prettyCStatement
  , prettyCType
  , prettyCExpr
  )
where

import Data.Foldable (fold)
import qualified Data.List as List
import Data.Text (Text)
import qualified Data.Text.Lazy as Lazy
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Word (Word64)
import GHC.Exts (fromString)
import Text.PrettyPrint.Leijen.Text (Doc)
import qualified Text.PrettyPrint.Leijen.Text as Pretty

newtype Ann = Ann Text
  deriving (Eq, Show)

data CType
  = Ptr CType
  | FunPtr CType (Vector CType)
  | Void (Maybe Ann)
  | Int32
  | UInt8
  | Bool
  | Name Text
  | TStruct (Vector (CType, Text))
  | Union (Vector (CType, Text))
  deriving (Eq, Show)

data CExpr
  = BTrue
  | BFalse
  | Alloca CExpr
  | Malloc CExpr
  | Number Integer
  | Var Text
  | Call CExpr (Vector CExpr)
  | Deref CExpr
  | Index CExpr Word64
  | Cast CType CExpr
  | Plus CExpr CExpr
  | Init (Vector CExpr)
  | InitNamed (Vector (Text, CExpr))
  | Project CExpr Text
  | Eq CExpr CExpr
  deriving (Eq, Show)

data CStatement
  = Return CExpr
  | Declare CType Text (Maybe CExpr)
  | Assign CExpr CExpr
  | If CExpr [CStatement]
  deriving (Eq, Show)

data CDecl
  = Include Text
  | Typedef CType Text
  | Struct Text (Vector (CType, Text))
  | Function CType Text (Vector (CType, Text)) [CStatement]
  deriving (Eq, Show)

newtype C = C [CDecl]
  deriving (Eq, Show, Semigroup, Monoid)

intersperseMap :: (Foldable f, Monoid m) => m -> (a -> m) -> f a -> m
intersperseMap sep f = fold . List.intersperse sep . foldr ((:) . f) []

render :: Doc -> Text
render = Lazy.toStrict . Pretty.displayT . Pretty.renderPretty 1.0 100

prettyCExpr :: CExpr -> Doc
prettyCExpr e =
  case e of
    BTrue -> "true"
    BFalse -> "false"
    Alloca a -> "alloca" <> Pretty.parens (prettyCExpr a)
    Malloc a -> "malloc" <> Pretty.parens (prettyCExpr a)
    Number a -> fromString $ show a
    Var a -> Pretty.textStrict a
    Call a bs ->
      (case a of
         Cast{} -> Pretty.parens
         Deref{} -> Pretty.parens
         Plus{} -> Pretty.parens
         _ -> id
      ) (prettyCExpr a) <>
      Pretty.parens (intersperseMap ", " prettyCExpr bs)
    Deref a ->
      "*" <>
      (case a of
         Plus{} -> Pretty.parens
         _ -> id)
      (prettyCExpr a)
    Index a n ->
      (case a of
         Cast{} -> Pretty.parens
         Plus{} -> Pretty.parens
         _ -> id)
      (prettyCExpr a) <>
      Pretty.brackets (fromString $ show n)
    Cast t a ->
      Pretty.parens (prettyCType t) <>
      (case a of
         Cast{} -> Pretty.parens
         Deref{} -> Pretty.parens
         Plus{} -> Pretty.parens
         _ -> id
      ) (prettyCExpr a)
    Plus a b ->
      prettyCExpr a <>
      " + " <>
      prettyCExpr b
    Init as -> Pretty.braces $ intersperseMap ", " prettyCExpr as
    InitNamed as ->
      Pretty.braces $
      intersperseMap
        ", "
        (\(a, b) -> "." <> Pretty.textStrict a <> " = " <> prettyCExpr b)
        as
    Project a b ->
      (case a of
         Cast{} -> Pretty.parens
         Plus{} -> Pretty.parens
         _ -> id
      )
      (prettyCExpr a) <>
      "." <> Pretty.textStrict b
    Eq a b ->
      prettyCExpr a <>
      " == " <>
      prettyCExpr b

prettyCType :: CType -> Doc
prettyCType t =
  case t of
    Ptr a -> prettyCType a <> " *"
    FunPtr ret args ->
      prettyCType ret <>
      Pretty.parens "*" <>
      Pretty.parens (intersperseMap ", " prettyCType args)
    Void m_ann  ->
      "void" <>
      foldMap (\(Ann a) -> " /* " <> Pretty.textStrict a <> " */") m_ann
    Int32 -> "int32_t"
    UInt8 -> "uint8_t"
    Bool -> "bool"
    Name n -> Pretty.textStrict n
    TStruct fs ->
      "struct " <>
      Pretty.braces
        (" " <>
         foldMap
           (\(ft, fn) -> prettyNamedCType fn ft <> "; ")
           fs
        )
    Union vs ->
      "union " <>
      Pretty.lbrace Pretty.<$>
      Pretty.indent 4
        (Pretty.vsep . Vector.toList $
         fmap
           (\(vt, vn) -> prettyNamedCType vn vt <> ";")
           vs
        ) Pretty.<$>
      Pretty.rbrace

prettyNamedCType :: Text -> CType -> Doc
prettyNamedCType n t =
  case t of
    FunPtr ret args ->
      prettyCType ret <>
      Pretty.parens ("*" <> Pretty.textStrict n) <>
      Pretty.parens (intersperseMap ", " prettyCType args)
    _ -> Pretty.hsep [prettyCType t, Pretty.textStrict n]

prettyCStatement :: CStatement -> Doc
prettyCStatement s =
  case s of
    Return e -> "return " <> prettyCExpr e
    Declare t n e ->
      prettyNamedCType n t <>
      foldMap ((" = " <>) . prettyCExpr) e
    Assign l r -> prettyCExpr l <> " = " <> prettyCExpr r
    If cond ss ->
      "if " <> Pretty.parens (prettyCExpr cond) <> " " <>
      Pretty.lbrace Pretty.<$>
      Pretty.indent 4
        (Pretty.vsep $
         fmap (\s' -> prettyCStatement s' <> ";") ss
        ) Pretty.<$>
      Pretty.rbrace

prettyCDecl :: CDecl -> Doc
prettyCDecl d =
  case d of
    Include n -> "#include " <> Pretty.textStrict n
    Function ty n args body ->
      prettyCType ty <> " " <> Pretty.textStrict n <>
      Pretty.parens
        (intersperseMap
          ", "
          (\(argTy, argName) ->
            prettyNamedCType argName argTy
          )
          args
        ) <>
      " " <>
      Pretty.lbrace Pretty.<$>
      Pretty.indent 4
        (Pretty.vsep $
         fmap (\s -> prettyCStatement s <> ";") body
        ) Pretty.<$>
      Pretty.rbrace
    Typedef t n ->
      "typedef " <> prettyCType t <> " " <> Pretty.textStrict n
    Struct n fs ->
      "struct " <> Pretty.textStrict n <> " " <>
      Pretty.lbrace Pretty.<$>
      Pretty.indent 4
        (Pretty.vsep . Vector.toList $
         fmap
           (\(ft, fn) -> prettyNamedCType fn ft <> ";")
           fs
        ) Pretty.<$>
      Pretty.rbrace

prettyCDecls :: [CDecl] -> Doc
prettyCDecls =
  intersperseMap
    Pretty.line
    (\d ->
       (case d of
          Typedef{} -> Pretty.line
          Function{} -> Pretty.line
          Struct{} -> Pretty.line
          _ -> mempty
       ) <>
       prettyCDecl d <>
       (case d of
          Typedef{} -> ";"
          Struct{} -> ";"
          Function{} -> ""
          _ -> mempty
       )
    )

preamble :: [CDecl]
preamble =
  [ Include "\"stdlib.h\""
  , Include "\"stdint.h\""
  , Include "\"stdbool.h\""
  , Include "\"alloca.h\""
  ]
