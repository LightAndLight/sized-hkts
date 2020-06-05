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
  , prettyCDecls
  , prettyCStatement
  , prettyCType
  , prettyCExpr
  )
where

import Data.Foldable (fold)
import qualified Data.List as List
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Vector (Vector)
import Data.Word (Word64)

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

intersperseMap :: Foldable f => Text -> (a -> Text) -> f a -> Text
intersperseMap sep f = fold . List.intersperse sep . foldr ((:) . f) []

parens :: Text -> Text
parens a = "(" <> a <> ")"

brackets :: Text -> Text
brackets a = "[" <> a <> "]"

prettyCExpr :: CExpr -> Text
prettyCExpr e =
  case e of
    BTrue -> "true"
    BFalse -> "false"
    Alloca a -> "alloca(" <> prettyCExpr a <> ")"
    Malloc a -> "malloc(" <> prettyCExpr a <> ")"
    Number a -> Text.pack $ show a
    Var a -> a
    Call a bs ->
      (case a of
         Cast{} -> parens
         Deref{} -> parens
         Plus{} -> parens
         _ -> id
      ) (prettyCExpr a) <>
      parens (intersperseMap ", " prettyCExpr bs)
    Deref a ->
      "*" <>
      (case a of
         Plus{} -> parens
         _ -> id)
      (prettyCExpr a)
    Index a n ->
      (case a of
         Cast{} -> parens
         Plus{} -> parens
         _ -> id)
      (prettyCExpr a) <>
      brackets (Text.pack $ show n)
    Cast t a ->
      parens (prettyCType t) <>
      (case a of
         Cast{} -> parens
         Deref{} -> parens
         Plus{} -> parens
         _ -> id
      ) (prettyCExpr a)
    Plus a b ->
      prettyCExpr a <>
      " + " <>
      prettyCExpr b
    Init as -> "{" <> intersperseMap ", " prettyCExpr as <> "}"
    InitNamed as -> "{" <> intersperseMap ", " (\(a, b) -> "." <> a <> " = " <> prettyCExpr b) as <> "}"
    Project a b ->
      (case a of
         Cast{} -> parens
         Plus{} -> parens
         _ -> id
      )
      (prettyCExpr a) <>
      "." <> b
    Eq a b ->
      prettyCExpr a <>
      " == " <>
      prettyCExpr b

prettyCType :: CType -> Text
prettyCType t =
  case t of
    Ptr a -> prettyCType a <> " *"
    FunPtr ret args -> "(" <> prettyCType ret <> ")*(" <> intersperseMap ", " prettyCType args <> ")"
    Void m_ann  ->
      "void" <> foldMap (\(Ann a) -> " /* " <> a <> " */") m_ann
    Int32 -> "int32_t"
    UInt8 -> "uint8_t"
    Bool -> "bool"
    Name n -> n
    TStruct fs ->
      "struct { " <>
      foldMap (\(ft, fn) -> prettyCType ft <> " " <> fn <> "; ") fs <>
      "}"
    Union vs ->
      "union {\n" <>
      foldMap
        (\(vt, vn) -> prettyCType vt <> " " <> vn <> ";\n")
        vs <>
      "}"

prettyCStatement :: CStatement -> Text
prettyCStatement s =
  case s of
    Return e -> "return " <> prettyCExpr e
    Declare t n e -> prettyCType t <> " " <> n <> foldMap ((" = " <>) . prettyCExpr) e
    Assign l r -> prettyCExpr l <> " = " <> prettyCExpr r
    If cond ss ->
      "if (" <> prettyCExpr cond <> ") {\n" <>
      foldMap (\s' -> prettyCStatement s' <> ";\n") ss <>
      "}"

prettyCDecl :: CDecl -> Text
prettyCDecl d =
  case d of
    Include n -> "#include " <> n
    Function ty n args body ->
      prettyCType ty <> " " <> n <>
      "(" <> intersperseMap ", " (\(argTy, argName) -> prettyCType argTy <> " " <> argName) args <> ") " <>
      "{\n\n" <>
      foldMap (\s -> prettyCStatement s <> ";\n") body <>
      "\n}"
    Typedef t n ->
      "typedef " <> prettyCType t <> " " <> n
    Struct n fs ->
      "struct " <> n <> " {\n" <>
      foldMap (\(ft, fn) -> prettyCType ft <> " " <> fn <> ";\n") fs <>
      "}"

prettyCDecls :: [CDecl] -> Text
prettyCDecls =
  intersperseMap
    "\n"
    (\d ->
       (case d of
          Typedef{} -> "\n"
          Function{} -> "\n"
          Struct{} -> "\n"
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
