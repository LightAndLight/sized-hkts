{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
module Codegen
  ( Code
  , emptyCode
  , codeKinds
  , codeDeclarations
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
import Data.Word (Word64)

import Check.Entailment
  ( Theory(..)
  , emptyEntailState, findSMeta, freshSMeta, solve
  )
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
  , _codeDeclarations :: Map Text IR.Declaration
  , _codeGlobalTheory :: Map (IR.Constraint Void) (Size Void)
  , _codeCompiledNames ::
      Map
        (Text, Vector (Syntax.Type Void))
        (Text, Maybe CDecl) -- Nothing indicates that this code is currently being compiled
  , _codeSupply :: Int
  }
makeLenses ''Code

emptyCode :: Code
emptyCode =
  Code
  { _codeKinds = mempty
  , _codeDeclarations = mempty
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
    Syntax.TApp _ _ ->
      C.Ptr . C.Void .
      Just $ C.Ann (Syntax.prettyType absurd ty)
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
    Syntax.TName n ->
      C.Ptr . C.Void .
      Just $ C.Ann n

genInst ::
  (MonadState Code m) =>
  Text ->
  Vector (Syntax.Type Void) ->
  m CExpr
genInst name ts = do
  m_code <- uses codeCompiledNames (Map.lookup (name, ts))
  name' <-
    case m_code of
      Nothing -> do
        let realName = name <> typeSuffix ts
        codeCompiledNames %= Map.insert (name, ts) (realName, Nothing)
        code <- do
          m_decl <- uses codeDeclarations $ Map.lookup name
          case m_decl of
            Nothing -> error $ "genInst: " <> show name <> " not found"
            Just decl ->
              case decl of
                IR.DFunc func -> genFunction func ts
                IR.DCtor{} -> error $ "genInst: got Ctor"
        codeCompiledNames %= Map.insert (name, ts) (realName, Just code)
        pure realName
      Just (realName, _) -> pure realName
  pure $ C.Var name'

genCtor ::
  (MonadState Code m) =>
  Text ->
  Vector (Syntax.Type Void) ->
  m CExpr
genCtor name ts = do
  m_code <- uses codeCompiledNames (Map.lookup (name, ts))
  name' <-
    case m_code of
      Nothing -> do
        let realName = name <> typeSuffix ts
        codeCompiledNames %= Map.insert (name, ts) (realName, Nothing)
        code <- do
          m_decl <- uses codeDeclarations $ Map.lookup name
          case m_decl of
            Nothing -> error $ "genCtor: " <> show name <> " not found"
            Just decl ->
              case decl of
                IR.DFunc{} -> error $ "genCtor: got Func"
                IR.DCtor ctor -> genConstructor ctor ts
        codeCompiledNames %= Map.insert (name, ts) (realName, Just code)
        pure realName
      Just (realName, _) -> pure realName
  pure $ C.Var name'

sizeOfType ::
  Map Text IR.Kind ->
  Map (IR.Constraint Void) (Size Void) ->
  Syntax.Type Void ->
  Word64
sizeOfType kindScope global t =
  case result of
    Left err -> error $ "sizeOfType: got " <> show err
    Right n -> n
  where
    result =
      flip evalStateT (emptyEntailState emptyTCState) $ do
        m <- freshSMeta
        (_, solutions) <-
          solve
            kindScope
            absurd
            absurd
            (Theory { _thGlobal = global, _thLocal = mempty })
            [(m, IR.CSized $ Right <$> t)]
        case findSMeta solutions m of
          Size.Word n -> pure n
          sz -> error $ "sizeOfType: got " <> show sz

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
        genBindings ::
          Vector ((Text, IR.Expr Void tm), Syntax.Type Void) ->
          WriterT [CStatement] m ()
        genBindings =
          traverse_
            (\((bname, bval), bty) -> do
               bval' <- genExpr vars bval
               tell [C.Declare (genType bty) bname bval']
            )
    IR.Inst n ts -> genInst n ts
    IR.Ctor{} -> error "genExpr: un-Call-ed Ctor"
    IR.Call (IR.Ctor n ts) bs retTy -> do
      n' <- genCtor n ts
      kindScope <- use codeKinds
      global <- use codeGlobalTheory
      let
        retTySize = sizeOfType kindScope global retTy
        retTyGen = genType retTy
      dest <- do
        d <- freshName
        tell
          [ C.Declare
              retTyGen
              d
              (C.Cast retTyGen .
               C.Alloca . C.Number $
               fromIntegral retTySize
              )
          ]
        pure $ C.Var d
      bs' <- traverse (genExpr vars) bs
      pure $ C.Call n' (Vector.cons dest bs')
    IR.Call a bs _ -> do
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
        size = sizeOfType kindScope global t
        pt = C.Ptr $ genType t
      n1 <- freshName
      tell
        [ C.Declare pt n1 . C.Cast pt $
          C.Malloc (C.Number $ fromIntegral size)
        , C.Assign (C.Deref $ C.Var n1) a'
        ]
      pure $ C.Var n1
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

genConstructor ::
  (MonadState Code m) =>
  IR.Constructor ->
  Vector (Syntax.Type Void) ->
  m CDecl
genConstructor (IR.Constructor name tyArgs args retTy) tyArgs' =
  let
    tyArgsLen = length tyArgs
  in
    case compare (Vector.length tyArgs') tyArgsLen of
      LT ->
        error $
        "genConstructor: not enough type arguments for " <>
        show name <>
        " (expected " <> show tyArgsLen <> ")"
      GT ->
        error $
        "genConstructor: too many type arguments for " <>
        show name <>
        " (expected " <> show tyArgsLen <> ")"
      EQ -> do
        kindScope <- use codeKinds
        global <- use codeGlobalTheory
        let
          inst = unvar (tyArgs' Vector.!) absurd
          args_inst = (fmap.fmap) (>>= inst) args
          retTy_inst = retTy >>= inst
          retTy_instGen = genType retTy_inst

          argSizes =
            fmap
              (\(_, argTy) -> sizeOfType kindScope global argTy)
              args_inst
        let argOffsets = Vector.init $ Vector.scanl (+) 0 argSizes
        destName <- freshName
        args_inst' <-
          traverse
            (\(m_n, t) -> (,) (genType t) <$> maybe freshName pure m_n)
            args_inst
        pure $
          C.Function
            retTy_instGen
            (name <> typeSuffix tyArgs')
            (Vector.cons (retTy_instGen, destName) $
             args_inst'
            )
            (foldr
               (\(offset, (t, n)) rest ->
                 C.Assign
                   (C.Deref $
                    C.Cast (C.Ptr t) $
                    C.Plus (C.Var destName) (C.Number $ fromIntegral offset)
                   )
                   (C.Var n) :
                 rest
               )
               [C.Return $ C.Var destName]
               (Vector.zip argOffsets args_inst')
            )

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
    (\(n, (_, m_decl)) rest ->
       case m_decl of
         Nothing -> error $ "genDecls: no decl for " <> show n
         Just decl -> pure $ decl : rest
    )
    []
    names
