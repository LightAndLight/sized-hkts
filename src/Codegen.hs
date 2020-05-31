{-# language BangPatterns #-}
{-# language FlexibleContexts #-}
{-# language OverloadedLists, OverloadedStrings #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
{-# language ViewPatterns #-}
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
import qualified Data.Maybe as Maybe
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
  , _codeDeclarations :: Map (IR.Origin, Text) IR.Declaration
  , _codeGlobalTheory :: Map (IR.Constraint Void) (Size Void)
  , _codeCompiledNames ::
      Map
        (IR.Origin, Text, Vector (Syntax.Type Void))
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

genType :: MonadState Code m => Syntax.Type Void -> m CType
genType ty =
  let
    (t, Vector.fromList -> ts) = Syntax.unApply ty
  in
    case t of
      Syntax.TVar a -> absurd a
      Syntax.TFun args | [ret] <- ts ->
        C.FunPtr <$>
        genType ret <*>
        traverse genType args
      Syntax.TPtr | [ret] <- ts ->
        C.Ptr <$> genType ret
      Syntax.TUInt ws ->
        case ws of
          Syntax.S8 -> pure C.Uint8
          Syntax.S16 -> pure C.Uint16
          Syntax.S32 -> pure C.Uint32
          Syntax.S64 -> pure C.Uint64
      Syntax.TInt ws ->
        case ws of
          Syntax.S8 -> pure C.Int8
          Syntax.S16 -> pure C.Int16
          Syntax.S32 -> pure C.Int32
          Syntax.S64 -> pure C.Int64
      Syntax.TBool -> pure C.Bool
      Syntax.TName name -> do
        let key = (IR.ODatatype, name, ts)
        m_code <- uses codeCompiledNames $ Map.lookup key
        name' <-
          case m_code of
            Nothing -> do
              let realName = name <> typeSuffix ts <> "_t"
              m_decl <- uses codeDeclarations $ Map.lookup (IR.ODatatype, name)
              codeCompiledNames %= Map.insert key (realName, Nothing)
              code <-
                case m_decl of
                  Nothing -> error $ "genType: " <> show name <> " not found"
                  Just decl ->
                    case decl of
                      IR.DData adt -> genDatatype adt ts
                      IR.DFunc{} -> error $ "genType: got Func"
                      IR.DCtor{} -> error $ "genInst: got Ctor"
              codeCompiledNames %= Map.insert key (realName, Just code)
              pure realName
            Just (realName, _) -> pure realName
        pure $ C.Name name'
      _ -> error $ "genType: bad type " <> show ty


genDatatype ::
  (MonadState Code m) =>
  IR.Datatype ->
  Vector (Syntax.Type Void) ->
  m CDecl
genDatatype adt ts =
  case adt of
    IR.Empty adtName tyArgs ->
      let
        !True = correctSize adtName (length tyArgs)
        fullName = adtName <> typeSuffix ts <> "_t"
      in
        pure $ C.Typedef (C.Void Nothing) fullName
    IR.Struct adtName tyArgs fields -> do
      let
        !True = correctSize adtName (length tyArgs)
        fullName = adtName <> typeSuffix ts <> "_t"

        fields_inst = (fmap.fmap) inst fields
        namedFields = nameFields fields_inst

      (\fs' -> C.Typedef (C.Struct fs') fullName) <$>
        traverse (\(n, t) -> (,) <$> genType t <*> pure n) namedFields
    IR.Enum adtName tyArgs ctors ->
      let
        !True = correctSize adtName (length tyArgs)
        fullName = adtName <> typeSuffix ts <> "_t"

        ctors_inst = (fmap.fmap.fmap.fmap) inst ctors
      in
        C.Union fullName <$>
        traverse
          (\(cname, cty) ->
             case Vector.length cty of
               0 -> pure (C.Void Nothing, cname)
               1 | (Nothing, ctyTy) <- cty Vector.! 0 -> do
                 (,) <$> genType ctyTy <*> pure cname
               _ ->
                 (,) . C.Struct <$>
                 traverse (\(n, t) -> (,) <$> genType t <*> pure n) (nameFields cty) <*>
                 pure cname
          )
          ctors_inst
  where
    nameFields fs =
      let
        numberedFieldNames = Text.pack . ('_' :) . show <$> [0..length fs-1]
      in
        Vector.zipWith (\n (m_n, t) -> (Maybe.fromMaybe n m_n, t)) numberedFieldNames fs

    inst = (>>= unvar (ts Vector.!) absurd)

    correctSize name tyArgsLen =
      case compare (Vector.length ts) tyArgsLen of
        LT ->
          error $
          "genDatatype: not enough type arguments for " <>
          show name <>
          " (expected " <> show tyArgsLen <> ")"
        GT ->
          error $
          "genDatatype: too many type arguments for " <>
          show name <>
          " (expected " <> show tyArgsLen <> ")"
        EQ -> True

genInst ::
  (MonadState Code m) =>
  Text ->
  Vector (Syntax.Type Void) ->
  m CExpr
genInst name ts = do
  let key = (IR.OFunction, name, ts)
  m_code <- uses codeCompiledNames $ Map.lookup key
  name' <-
    case m_code of
      Nothing -> do
        let realName = name <> typeSuffix ts
        codeCompiledNames %= Map.insert key (realName, Nothing)
        code <- do
          m_decl <- uses codeDeclarations $ Map.lookup (IR.OFunction, name)
          case m_decl of
            Nothing -> error $ "genInst: " <> show name <> " not found"
            Just decl ->
              case decl of
                IR.DFunc func -> genFunction func ts
                IR.DData{} -> error $ "genInst: got Data"
                IR.DCtor{} -> error $ "genInst: got Ctor"
        codeCompiledNames %= Map.insert key (realName, Just code)
        pure realName
      Just (realName, _) -> pure realName
  pure $ C.Var name'

genCtor ::
  (MonadState Code m) =>
  Text ->
  Vector (Syntax.Type Void) ->
  m CExpr
genCtor name ts = do
  let key = (IR.OConstructor, name, ts)
  m_code <- uses codeCompiledNames $ Map.lookup key
  name' <-
    case m_code of
      Nothing -> do
        let realName = "make_" <> name <> typeSuffix ts
        codeCompiledNames %= Map.insert key (realName, Nothing)
        code <- do
          m_decl <- uses codeDeclarations $ Map.lookup (IR.OConstructor, name)
          case m_decl of
            Nothing -> error $ "genCtor: " <> show name <> " not found"
            Just decl ->
              case decl of
                IR.DFunc{} -> error $ "genCtor: got Func"
                IR.DCtor ctor -> genConstructor ctor ts
                IR.DData{} -> error $ "genCtor: got Data"
        codeCompiledNames %= Map.insert key (realName, Just code)
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
               bty' <- genType bty
               tell [C.Declare bty' bname bval']
            )
    IR.Inst n ts -> genInst n ts
    IR.Ctor n ts -> genCtor n ts
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
      pt <- C.Ptr <$> genType t
      n1 <- freshName
      tell
        [ C.Declare pt n1 . C.Cast pt $
          C.Malloc (C.Number $ fromIntegral size)
        , C.Assign (C.Deref $ C.Var n1) a'
        ]
      pure $ C.Var n1
    IR.Deref a -> C.Deref <$> genExpr vars a
    IR.Project a b -> do
      a' <- genExpr vars a
      case b of
        IR.Numeric ix ->
          pure $ C.Project a' (Text.pack $ '_' : show ix)
        IR.Field n ->
          pure $ C.Project a' n

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
        let
          inst = unvar (tyArgs' Vector.!) absurd
          args_inst = (fmap.fmap) (>>= inst) args
          retTy_inst = retTy >>= inst

        retTy_instGen <- genType retTy_inst
        args_inst' <-
          traverse
            (\(m_n, t) -> (,) <$> genType t <*> maybe freshName pure m_n)
            args_inst
        destName <- freshName
        pure $
          C.Function
            retTy_instGen
            ("make_" <> name <> typeSuffix tyArgs')
            args_inst'
            [ C.Declare retTy_instGen destName . C.Init $ C.Var . snd <$> args_inst'
            , C.Return $ C.Var destName
            ]

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
        (\retTy' args' ->
           C.Function retTy'
             (name <> typeSuffix tyArgs')
             args'
             (sts <> [C.Return body'])
          ) <$>
           genType retTy_inst <*>
           traverse (\(n, t) -> (,) <$> genType t <*> pure n) args_inst

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
