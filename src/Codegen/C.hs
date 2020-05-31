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
  | Uint8
  | Uint16
  | Uint32
  | Uint64
  | Int8
  | Int16
  | Int32
  | Int64
  | Bool
  | Name Text
  | Struct (Vector (CType, Text))
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
  deriving (Eq, Show)

data CStatement
  = Return CExpr
  | Declare CType Text CExpr
  | Assign CExpr CExpr
  deriving (Eq, Show)

data CDecl
  = Include Text
  | Union Text (Vector (CType, Text))
  | Typedef CType Text
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
         Plus{} -> parens
         _ -> id
      ) (prettyCExpr a)
    Plus a b ->
      prettyCExpr a <>
      " + " <>
      prettyCExpr b
    Init as -> "{" <> intersperseMap ", " prettyCExpr as <> "}"

prettyCType :: CType -> Text
prettyCType t =
  case t of
    Ptr a -> prettyCType a <> " *"
    FunPtr ret args -> "(" <> prettyCType ret <> ")*(" <> intersperseMap ", " prettyCType args <> ")"
    Void m_ann  ->
      "void" <> foldMap (\(Ann a) -> " /* " <> a <> " */") m_ann
    Uint8 -> "uint8_t"
    Uint16 -> "uint16_t"
    Uint32 -> "uint32_t"
    Uint64 -> "uint64_t"
    Int8 -> "int8_t"
    Int16 -> "int16_t"
    Int32 -> "int32_t"
    Int64 -> "int64_t"
    Bool -> "bool"
    Name n -> n
    Struct fs ->
      "struct { " <>
      foldMap (\(ft, fn) -> prettyCType ft <> " " <> fn <> "; ") fs <>
      "}"

prettyCStatement :: CStatement -> Text
prettyCStatement s =
  case s of
    Return e -> "return " <> prettyCExpr e
    Declare t n e -> prettyCType t <> " " <> n <> " = " <> prettyCExpr e
    Assign l r -> prettyCExpr l <> " = " <> prettyCExpr r

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
    Union n vs ->
      "typedef union " <> n <> "{\n" <>
      foldMap
        (\(vt, vn) -> prettyCType vt <> " " <> vn <> ";\n")
        vs <>
      "} " <> n

prettyCDecls :: [CDecl] -> Text
prettyCDecls =
  intersperseMap
    "\n"
    (\d ->
       (case d of
          Typedef{} -> "\n"
          Function{} -> "\n"
          Union{} -> "\n"
          _ -> mempty
       ) <>
       prettyCDecl d <>
       (case d of
          Typedef{} -> ";"
          Function{} -> ""
          Union{} -> ""
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
