{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
module Codegen
  ( Code
  , genFunction
  , genExpr
  )
where

import Bound.Var (unvar)
import Control.Lens.Getter (use, uses)
import Control.Lens.Setter ((.=), (%=))
import Control.Lens.TH (makeLenses)
import Control.Monad.State (MonadState)
import Control.Monad.Writer (WriterT, tell)
import Data.Foldable (foldrM, traverse_)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Void (Void, absurd)

import Codegen.C (C, CDecl, CExpr, CStatement, CType)
import qualified Codegen.C as C
import qualified IR
import qualified Syntax

data Code
  = Code
  { _codeFunctions :: Map Text IR.Function
  , _codeCompiledNames ::
      Map
        (Text, Vector (Syntax.Type Void))
        (Maybe CDecl) -- Nothing indicates that this code is currently being compiled
  , _codeSupply :: Int
  }
makeLenses ''Code

freshName :: MonadState Code m => m Text
freshName = do
  n <- use codeSupply
  codeSupply .= (n+1)
  pure . Text.pack $ "__" <> show n

genType :: Syntax.Type Void -> CType
genType ty =
  case ty of
    Syntax.TVar a -> absurd a
    Syntax.TApp (Syntax.TFun args) ret -> C.FunPtr (genType ret) (genType <$> args)
    Syntax.TApp Syntax.TPtr ret -> C.Ptr (genType ret)
    Syntax.TApp _ _ -> C.Void $ C.Ann (Syntax.prettyType absurd ty)
    Syntax.TUInt ws ->
      case ws of
        Syntax.S8 -> C.Uint8
        Syntax.S16 -> C.Uint16
        Syntax.S32 -> C.Uint32
        Syntax.S64 -> C.Uint64
    Syntax.TInt ws ->
      case ws of
        Syntax.S8 -> C.Int8
        Syntax.S16 -> C.Int16
        Syntax.S32 -> C.Int32
        Syntax.S64 -> C.Int64
    Syntax.TBool -> C.Bool
    Syntax.TPtr -> error "genType: unapplied TPtr"
    Syntax.TFun{} -> error "genType: unapplied TFun"
    Syntax.TName n -> C.Void $ C.Ann n

genInst ::
  (MonadState Code m) =>
  Text ->
  Vector (Syntax.Type Void) ->
  m CExpr
genInst name ts = do
  m_code <- uses codeCompiledNames (Map.lookup (name, ts))
  case m_code of
    Nothing -> do
      codeCompiledNames %= Map.insert (name, ts) Nothing
      code <- do
        m_func <- uses codeFunctions $ Map.lookup name
        case m_func of
          Nothing -> error $ "genInst: " <> show name <> " not found"
          Just func -> genFunction func ts
      codeCompiledNames %= Map.insert (name, ts) (Just code)
    Just{} -> pure ()
  pure $ C.Var name

genExpr ::
  forall m tm.
  (MonadState Code m) =>
  (tm -> Text) ->
  IR.Expr Void tm ->
  WriterT [CStatement] m CExpr
genExpr vars expr =
  case expr of
    IR.Var a -> pure $ C.Var (vars a)
    IR.Name n -> pure $ C.Var n
    IR.Let es b -> do
      genBindings es
      genExpr vars b
      where
        genBindings :: Vector (Text, IR.Expr Void tm) -> WriterT [CStatement] m ()
        genBindings =
          traverse_
            (\(bname, bval) -> do
               bval' <- genExpr vars bval
               tell [C.Assign _ bname bval']
            )
    IR.Inst n ts -> genInst n ts
    IR.Call a bs -> do
      a' <- genExpr vars a
      bs' <- traverse (genExpr vars) bs
      pure $ C.Call a' bs'
    IR.UInt8 n -> pure . C.Number $ fromIntegral n
    IR.UInt16 n -> pure . C.Number $ fromIntegral n
    IR.UInt32 n -> pure . C.Number $ fromIntegral n
    IR.UInt64 n -> pure . C.Number $ fromIntegral n
    IR.Int8 n -> pure . C.Number $ fromIntegral n
    IR.Int16 n -> pure . C.Number $ fromIntegral n
    IR.Int32 n -> pure . C.Number $ fromIntegral n
    IR.Int64 n -> pure . C.Number $ fromIntegral n
    IR.BTrue -> pure C.BTrue
    IR.BFalse -> pure C.BFalse
    IR.New a -> C.Malloc <$> _ a
    IR.Deref a -> C.Deref <$> genExpr vars a

genFunction ::
  (MonadState Code m) =>
  IR.Function ->
  Vector (Syntax.Type Void) ->
  m CDecl
genFunction (IR.Function name tyArgs constraints args retTy body) tyArgs' =
  let
    tyArgsLen = length tyArgs
  in
    case compare (Vector.length tyArgs') tyArgsLen of
      LT ->
        error $
        "genFunction: not enough type arguments for " <>
        show name <>
        " (expected " <> show tyArgsLen <> ")"
      GT ->
        error $
        "genFunction: too many type arguments for " <>
        show name <>
        " (expected " <> show tyArgsLen <> ")"
      EQ -> do
        let
          inst = unvar (tyArgs' Vector.!) absurd
          constraints_inst = IR.bindConstraint inst <$> constraints
          args_inst = (fmap.fmap) (>>= inst) args
          retTy_inst = retTy >>= inst
          body_inst = IR.bindType_Expr inst body
        body' <- genExpr _ body_inst
        pure $
          C.Function
            (genType retTy_inst)
            name
            ((\(n, t) -> (genType t, n)) <$> args_inst)
            body'
