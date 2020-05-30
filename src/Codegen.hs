{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
module Codegen
  ( Code
  , emptyCode
  , codeKinds
  , codeFunctions
  , codeGlobalTheory
  , genFunction
  , genExpr
  , genDecls
  )
where

import Bound.Var (unvar)
import Control.Lens.Getter (use, uses)
import Control.Lens.Setter ((.=), (%=))
import Control.Lens.TH (makeLenses)
import Control.Monad.State (MonadState, evalStateT)
import Control.Monad.Writer (WriterT, runWriterT, tell)
import Data.Foldable (fold, foldrM, traverse_)
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Void (Void, absurd)

import Check.Entailment (Theory(..), emptyEntailState, findSMeta, freshSMeta, solve)
import Codegen.C (CDecl, CExpr, CStatement, CType)
import qualified Codegen.C as C
import qualified IR
import TCState (emptyTCState)
import Size (Size)
import qualified Size
import qualified Syntax

data Code
  = Code
  { _codeKinds :: Map Text IR.Kind
  , _codeFunctions :: Map Text IR.Function
  , _codeGlobalTheory :: Map (IR.Constraint Void) (Size Void)
  , _codeCompiledNames ::
      Map
        (Text, Vector (Syntax.Type Void))
        (Maybe CDecl) -- Nothing indicates that this code is currently being compiled
  , _codeSupply :: Int
  }
makeLenses ''Code

emptyCode :: Code
emptyCode =
  Code
  { _codeKinds = mempty
  , _codeFunctions = mempty
  , _codeGlobalTheory = mempty
  , _codeCompiledNames = mempty
  , _codeSupply = 0
  }

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
        genBindings :: Vector ((Text, IR.Expr Void tm), Syntax.Type Void) -> WriterT [CStatement] m ()
        genBindings =
          traverse_
            (\((bname, bval), bty) -> do
               bval' <- genExpr vars bval
               tell [C.Declare (genType bty) bname bval']
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
    IR.New a t -> do
      a' <- genExpr vars a
      kindScope <- use codeKinds
      global <- use codeGlobalTheory
      let
        m_size =
          flip evalStateT (emptyEntailState emptyTCState) $ do
            m <- freshSMeta
            (_, solutions) <-
              solve
                kindScope
                absurd
                absurd
                (Theory { _thGlobal = global, _thLocal = mempty })
                [(m, IR.CSized $ Right <$> t)]
            pure $ findSMeta solutions m
      case m_size of
        Left err -> error $ "genExpr: solve failed with " <> show err
        Right size ->
          case size of
            Size.Word n -> do
              let pt = C.Ptr $ genType t
              n1 <- freshName
              tell
                [ C.Declare pt n1 . C.Cast pt $
                  C.Malloc (C.Number $ fromIntegral n)
                , C.Assign (C.Deref $ C.Var n1) a'
                ]
              pure $ C.Var n1
            _ -> error $ "genExpr: " <> show size <> " is not a Word"
    IR.Deref a -> C.Deref <$> genExpr vars a

typeSuffix :: Vector (Syntax.Type Void) -> Text
typeSuffix ts =
  if Vector.null ts
  then mempty
  else
    ("_" <>) . fold . List.intersperse "_" $ foldr ((:) . doTy) [] ts
  where
    doTy ty =
      case ty of
        Syntax.TVar a -> absurd a
        Syntax.TApp t1 t2 -> "TApp" <> doTy t1 <> doTy t2
        Syntax.TUInt ws -> "TUInt" <> Text.pack (show $ 8 * Syntax.wordSize ws)
        Syntax.TInt ws -> "TInt" <> Text.pack (show $ 8 * Syntax.wordSize ws)
        Syntax.TBool -> "TBool"
        Syntax.TPtr -> "TPtr"
        Syntax.TFun args -> "TFun" <> foldMap doTy args
        Syntax.TName a -> a

genFunction ::
  (MonadState Code m) =>
  IR.Function ->
  Vector (Syntax.Type Void) ->
  m CDecl
genFunction (IR.Function name tyArgs _constraints args retTy body) tyArgs' =
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
          -- constraints_inst = IR.bindConstraint inst <$> _constraints
          args_inst = (fmap.fmap) (>>= inst) args
          retTy_inst = retTy >>= inst
          body_inst = IR.bindType_Expr inst body
        (body', sts) <- runWriterT $ genExpr (unvar (fmap fst args Vector.!) absurd) body_inst
        pure $
          C.Function
            (genType retTy_inst)
            (name <> typeSuffix tyArgs')
            ((\(n, t) -> (genType t, n)) <$> args_inst)
            (sts <> [C.Return body'])

genDecls :: MonadState Code m => m [CDecl]
genDecls = do
  names <- uses codeCompiledNames Map.toList
  foldrM
    (\(n, m_decl) rest ->
       case m_decl of
         Nothing -> error $ "genDecls: no decl for " <> show n
         Just decl -> pure $ decl : rest
    )
    []
    names
