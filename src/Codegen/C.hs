{-# language GeneralizedNewtypeDeriving #-}
module Codegen.C
  ( Ann(..)
  , C(..)
  , CDecl(..)
  , CStatement(..)
  , CType(..)
  , CExpr(..)
  )
where

import Data.Text (Text)
import Data.Vector (Vector)

newtype Ann = Ann Text
  deriving (Eq, Show)

data CType
  = Ptr CType
  | FunPtr CType (Vector CType)
  | Void Ann
  | Uint8
  | Uint16
  | Uint32
  | Uint64
  | Int8
  | Int16
  | Int32
  | Int64
  | Bool
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
  | Cast CType CExpr
  deriving (Eq, Show)

data CStatement
  = Return CExpr
  | Declare CType Text CExpr
  | Assign CExpr CExpr
  deriving (Eq, Show)

data CDecl
  = Include Text
  | Function CType Text (Vector (CType, Text)) [CStatement]
  deriving (Eq, Show)

newtype C = C [CDecl]
  deriving (Eq, Show, Semigroup, Monoid)
