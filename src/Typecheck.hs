{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
module Typecheck where

import Bound.Var (Var(..), unvar)
import Control.Monad.Except (MonadError, ExceptT(..), runExceptT, throwError)
import Control.Monad.State (MonadState, evalStateT, gets, modify)
import Data.Foldable (foldl', foldlM)
import Data.Int (Int8, Int16, Int32, Int64)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Void (Void, absurd)
import Data.Word (Word8, Word16, Word32, Word64)

import Syntax (Type)
import qualified Syntax
import IR (KMeta(..), Kind(..), TypeScheme)
import qualified IR

data TypeError
  = MissingKMeta KMeta
  | MissingTMeta TMeta
  | NotNumeric (TypeM Text)
  | OutOfBoundsUnsigned Syntax.WordSize Integer
  | OutOfBoundsSigned Syntax.WordSize Integer
  | TypeMismatch (TypeM Text) (TypeM Text)
  | Occurs TMeta (TypeM Text)
  | Can'tInfer (Syntax.Expr Text)
  | NotInScope Text
  deriving Show

newtype TMeta = TMeta Int
  deriving (Eq, Ord, Show)

data TCState
  = TCState
  { tcsKindMeta :: KMeta
  , tcsTypeMeta :: TMeta
  , tcsTypeMetaKinds :: Map TMeta Kind
  }

emptyTCState :: TCState
emptyTCState =
  TCState
  { tcsKindMeta = KMeta 0
  , tcsTypeMeta = TMeta 0
  , tcsTypeMetaKinds = mempty
  }

freshKMeta :: MonadState TCState m => m KMeta
freshKMeta = do
  KMeta k <- gets tcsKindMeta
  modify $ \s -> s { tcsKindMeta = KMeta (k+1) }
  pure $ KMeta k

freshTMeta :: MonadState TCState m => Kind -> m TMeta
freshTMeta k = do
  TMeta t <- gets tcsTypeMeta
  modify $ \s -> s { tcsTypeMeta = TMeta (t+1), tcsTypeMetaKinds = Map.insert (TMeta t) k (tcsTypeMetaKinds s) }
  pure $ TMeta t

type TypeM = ExceptT TMeta Type
pattern TypeM :: Type (Either TMeta ty) -> TypeM ty
pattern TypeM a = ExceptT a
unTypeM :: TypeM ty -> Type (Either TMeta ty)
unTypeM = runExceptT

applyTSubs :: Map TMeta (TypeM ty) -> TypeM ty -> TypeM ty
applyTSubs subs ty =
  TypeM $
  unTypeM ty >>=
  either
    (\m -> maybe (Syntax.TVar $ Left m) unTypeM $ Map.lookup m subs)
    (Syntax.TVar . Right)

applyTSubs_Expr ::
  Map TMeta (TypeM ty) ->
  IR.Expr (Either TMeta ty) tm ->
  IR.Expr (Either TMeta ty) tm
applyTSubs_Expr subs expr =
  case expr of
    IR.Var{} -> expr
    IR.Name{} -> expr
    IR.Let bindings body ->
      IR.Let ((fmap.fmap) (applyTSubs_Expr subs) bindings) (applyTSubs_Expr subs body)
    IR.Inst n tyArgs ->
      IR.Inst n (unTypeM . applyTSubs subs . TypeM <$> tyArgs)
    IR.Call f args ->
      IR.Call (applyTSubs_Expr subs f) (applyTSubs_Expr subs <$> args)
    IR.UInt8{} -> expr
    IR.UInt16{} -> expr
    IR.UInt32{} -> expr
    IR.UInt64{} -> expr
    IR.Int8{} -> expr
    IR.Int16{} -> expr
    IR.Int32{} -> expr
    IR.Int64{} -> expr
    IR.BTrue -> expr
    IR.BFalse -> expr
    IR.Deref a -> IR.Deref (applyTSubs_Expr subs a)
    IR.New a -> IR.New (applyTSubs_Expr subs a)

applyTSubs_Constraint ::
  Map TMeta (TypeM ty) ->
  IR.Constraint (Either TMeta ty) ->
  IR.Constraint (Either TMeta ty)
applyTSubs_Constraint subs =
  IR.bindConstraint (either (\m -> maybe (pure $ Left m) unTypeM $ Map.lookup m subs) (pure . Right))

applyKSubs :: Map KMeta Kind -> Kind -> Kind
applyKSubs subs k =
  case k of
    KVar m ->
      case Map.lookup m subs of
        Nothing -> k
        Just k' -> k'
    KArr a b -> KArr (applyKSubs subs a) (applyKSubs subs b)
    KType -> KType

composeKSubs ::
  Map KMeta Kind ->
  Map KMeta Kind ->
  Map KMeta Kind
composeKSubs a b =
  fmap (applyKSubs a) b <> a

composeTSubs ::
  Map TMeta (TypeM ty) ->
  Map TMeta (TypeM ty) ->
  Map TMeta (TypeM ty)
composeTSubs a b =
  fmap (applyTSubs a) b <> a

unifyType ::
  (MonadError TypeError m, Eq ty) =>
  (ty -> Text) ->
  (ty -> Kind) ->
  TypeM ty ->
  TypeM ty ->
  m (Map TMeta (TypeM ty))
unifyType tyNames kinds expected actual =
  case unTypeM expected of
    Syntax.TVar (Left m) -> solveLeft m actual
    Syntax.TVar (Right a) ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TVar (Right b) ->
          if a == b
          then pure mempty
          else throwError $ TypeMismatch (tyNames <$> expected) (tyNames <$> actual)
        _ -> throwError $ TypeMismatch (tyNames <$> expected) (tyNames <$> actual)
    Syntax.TApp a b ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TApp a' b' -> do
          sols1 <- unifyType tyNames kinds (TypeM a) (TypeM a')
          sols2 <- unifyType tyNames kinds (applyTSubs sols1 $ TypeM b) (applyTSubs sols1 $ TypeM b')
          pure $ composeTSubs sols2 sols1
        _ -> throwError $ TypeMismatch (tyNames <$> expected) (tyNames <$> actual)
    Syntax.TUInt sz ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TUInt sz' | sz == sz' -> pure mempty
        _ -> throwError $ TypeMismatch (tyNames <$> expected) (tyNames <$> actual)
    Syntax.TInt sz ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TInt sz' | sz == sz' -> pure mempty
        _ -> throwError $ TypeMismatch (tyNames <$> expected) (tyNames <$> actual)
    Syntax.TBool ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TBool -> pure mempty
        _ -> throwError $ TypeMismatch (tyNames <$> expected) (tyNames <$> actual)
    Syntax.TPtr ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TPtr -> pure mempty
        _ -> throwError $ TypeMismatch (tyNames <$> expected) (tyNames <$> actual)
    Syntax.TFun args ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TFun args' | Vector.length args == Vector.length args' ->
          foldl' composeTSubs mempty <$>
          traverse
            (\(a, b) -> unifyType tyNames kinds (TypeM a) (TypeM b))
            (Vector.zip args args')
        _ -> throwError $ TypeMismatch (tyNames <$> expected) (tyNames <$> actual)
    Syntax.TName n ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TName n' | n == n' -> pure mempty
        _ -> throwError $ TypeMismatch (tyNames <$> expected) (tyNames <$> actual)
  where
    solveLeft m actual' =
      case unTypeM actual' of
        Syntax.TVar (Left m') | m == m' -> pure mempty
        _ ->
          if any (either (== m) (const False)) (unTypeM actual')
          then throwError $ Occurs m (tyNames <$> actual')
          else pure $ Map.singleton m actual'
    solveRight expected' m =
      case unTypeM expected' of
        Syntax.TVar (Left m') | m == m' -> pure mempty
        _ ->
          if any (either (== m) (const False)) (unTypeM expected')
          then throwError $ Occurs m (tyNames <$> expected')
          else pure $ Map.singleton m expected'

data InferResult ty tm
  = InferResult
  { irExpr :: IR.Expr (Either TMeta ty) tm
  , irType :: TypeM ty
  , irConstraints :: Set (IR.Constraint (Either TMeta ty))
  , irKindSols :: Map KMeta Kind
  , irTypeSols :: Map TMeta (TypeM ty)
  }

instantiateScheme ::
  MonadState TCState m =>
  TypeScheme Void ->
  m ([TMeta], Vector (IR.Constraint (Either TMeta ty)), TypeM ty)
instantiateScheme = go (Right . absurd)
  where
    go ::
      MonadState TCState m =>
      (x -> Either TMeta ty) ->
      TypeScheme x ->
      m ([TMeta], Vector (IR.Constraint (Either TMeta ty)), TypeM ty)
    go var scheme =
      case scheme of
        IR.SForall _ k rest -> do
          meta <- freshTMeta k
          (ms, cs, ty) <- go (unvar (\() -> Left meta) var) rest
          pure (meta:ms, cs, ty)
        IR.SDone constraints argTys ty ->
          pure
            ( []
            , (fmap.fmap) var constraints
            , TypeM $
              Syntax.TApp
                (Syntax.TFun $ fmap var <$> argTys)
                (var <$> ty)
            )

inferExpr ::
  (MonadState TCState m, MonadError TypeError m, Ord ty) =>
  Map Text (TypeScheme Void) ->
  Map Text (TypeM ty) ->
  (ty -> Text) ->
  (tm -> Text) ->
  (ty -> Kind) ->
  (tm -> TypeM ty) ->
  Syntax.Expr tm ->
  m (InferResult ty tm)
inferExpr tyScope letScope tyNames tmNames kinds types expr =
  case expr of
    Syntax.Var a ->
      pure $
      InferResult
      { irExpr = IR.Var a
      , irType = types a
      , irConstraints = mempty
      , irKindSols = mempty
      , irTypeSols = mempty
      }

    Syntax.Name name -> do
      case Map.lookup name letScope of
        Nothing ->
          case Map.lookup name tyScope of
            Nothing -> throwError $ NotInScope name
            Just scheme -> do
              (metas, constraints, bodyTy) <- instantiateScheme scheme
              pure $
                InferResult
                { irExpr = IR.Inst name $ Syntax.TVar . Left <$> Vector.fromList metas
                , irType = bodyTy
                , irConstraints = foldr Set.insert mempty constraints
                , irKindSols = mempty
                , irTypeSols = mempty
                }
        Just ty ->
          pure $
            InferResult
            { irExpr = IR.Name name
            , irType = ty
            , irConstraints = mempty
            , irKindSols = mempty
            , irTypeSols = mempty
            }

    Syntax.Let bindings body -> do
      (letScope', bindings', constraints, kSols, tSols) <-
        foldlM
          (\(acc, bs, cs, ksols, tsols) (n, b) -> do
             bResult <- inferExpr tyScope acc tyNames tmNames kinds types b
             pure
               ( Map.insert n (irType bResult) acc
               , Vector.snoc bs (n, irExpr bResult)
               , irConstraints bResult <> cs
               , composeKSubs (irKindSols bResult) ksols
               , composeTSubs (irTypeSols bResult) tsols
               )
          )
          (mempty, mempty, mempty, mempty, mempty)
          bindings
      bodyResult <- inferExpr tyScope letScope' tyNames tmNames kinds types body
      pure $
        InferResult
        { irExpr = IR.Let bindings' $ irExpr bodyResult
        , irType = irType bodyResult
        , irConstraints = irConstraints bodyResult <> constraints
        , irKindSols = composeKSubs (irKindSols bodyResult) kSols
        , irTypeSols = composeTSubs (irTypeSols bodyResult) tSols
        }

    Syntax.Call fun args -> do
      funResult <- inferExpr tyScope letScope tyNames tmNames kinds types fun
      (args', argTys, constraints, ksols, tsols) <-
        foldlM
          (\(as, atys, cs, ks, ts) arg -> do
             argResult <- inferExpr tyScope letScope tyNames tmNames kinds types arg
             pure
               ( Vector.snoc as $ irExpr argResult
               , Vector.snoc atys . unTypeM $ irType argResult
               , irConstraints argResult <> cs
               , composeKSubs (irKindSols argResult) ks
               , composeTSubs (irTypeSols argResult) ts
               )
          )
          (mempty, mempty, irConstraints funResult, irKindSols funResult, irTypeSols funResult)
          args
      meta <- freshTMeta KType
      subs <-
        unifyType
          tyNames
          kinds
          (TypeM $ Syntax.TApp (Syntax.TFun argTys) (Syntax.TVar $ Left meta))
          (irType funResult)
      pure $
        InferResult
        { irExpr = IR.Call (irExpr funResult) args'
        , irType = applyTSubs subs (TypeM . Syntax.TVar $ Left meta)
        , irConstraints = constraints
        , irKindSols = ksols
        , irTypeSols = composeTSubs subs tsols
        }

    Syntax.Number{} -> throwError $ Can'tInfer (tmNames <$> expr)

    Syntax.BTrue ->
      pure $
      InferResult
      { irExpr = IR.BTrue
      , irType = TypeM Syntax.TBool
      , irConstraints = mempty
      , irKindSols = mempty
      , irTypeSols = mempty
      }

    Syntax.BFalse ->
      pure $
      InferResult
      { irExpr = IR.BTrue
      , irType = TypeM Syntax.TBool
      , irConstraints = mempty
      , irKindSols = mempty
      , irTypeSols = mempty
      }

    Syntax.New a -> do
      aResult <- inferExpr tyScope letScope tyNames tmNames kinds types a
      pure $
        InferResult
        { irExpr = IR.New $ irExpr aResult
        , irType = TypeM $ Syntax.TApp Syntax.TPtr (unTypeM $ irType aResult)
        , irConstraints = irConstraints aResult
        , irKindSols = irKindSols aResult
        , irTypeSols = irTypeSols aResult
        }

    Syntax.Deref a -> do
      aResult <- inferExpr tyScope letScope tyNames tmNames kinds types a
      meta <- freshTMeta KType
      subs <-
        unifyType
          tyNames
          kinds
          (TypeM $ Syntax.TApp Syntax.TPtr $ Syntax.TVar $ Left meta)
          (irType aResult)
      pure $
        InferResult
        { irExpr =
            applyTSubs_Expr subs $
            IR.Deref (irExpr aResult)
        , irType =
            applyTSubs subs $
            TypeM (Syntax.TVar $ Left meta)
        , irConstraints = irConstraints aResult
        , irKindSols = irKindSols aResult
        , irTypeSols = composeTSubs subs (irTypeSols aResult)
        }

data CheckResult ty tm
  = CheckResult
  { crExpr :: IR.Expr (Either TMeta ty) tm
  , crKindSols :: Map KMeta Kind
  , crTypeSols :: Map TMeta (TypeM ty)
  }

checkExpr ::
  (MonadState TCState m, MonadError TypeError m, Ord ty) =>
  Map Text (TypeScheme Void) ->
  Map Text (TypeM ty) ->
  (ty -> Text) ->
  (tm -> Text) ->
  (ty -> Kind) ->
  (tm -> TypeM ty) ->
  Syntax.Expr tm ->
  TypeM ty ->
  m (CheckResult ty tm)
checkExpr tyScope letScope tyNames tmNames kinds types expr ty =
  case expr of
    Syntax.Number n ->
      case unTypeM ty of
        Syntax.TUInt sz ->
          case sz of
            Syntax.S8 ->
              if 0 <= n && n <= fromIntegral (maxBound::Word8)
              then
                pure $
                CheckResult
                { crExpr = IR.UInt8 (fromIntegral n)
                , crKindSols = mempty
                , crTypeSols = mempty
                }
              else throwError $ OutOfBoundsUnsigned sz n
            Syntax.S16 ->
              if 0 <= n && n <= fromIntegral (maxBound::Word16)
              then
                pure $
                CheckResult
                { crExpr = IR.UInt16 (fromIntegral n)
                , crKindSols = mempty
                , crTypeSols = mempty
                }
              else throwError $ OutOfBoundsUnsigned sz n
            Syntax.S32 ->
              if 0 <= n && n <= fromIntegral (maxBound::Word32)
              then
                pure $
                CheckResult
                { crExpr = IR.UInt32 (fromIntegral n)
                , crKindSols = mempty
                , crTypeSols = mempty
                }
              else throwError $ OutOfBoundsUnsigned sz n
            Syntax.S64 ->
              if 0 <= n && n <= fromIntegral (maxBound::Word64)
              then
                pure $
                CheckResult
                { crExpr = IR.UInt64 (fromIntegral n)
                , crKindSols = mempty
                , crTypeSols = mempty
                }
              else throwError $ OutOfBoundsUnsigned sz n
        Syntax.TInt sz ->
          case sz of
            Syntax.S8 ->
              if 0 <= n && n <= fromIntegral (maxBound::Int8)
              then
                pure $
                CheckResult
                { crExpr = IR.Int8 (fromIntegral n)
                , crKindSols = mempty
                , crTypeSols = mempty
                }
              else throwError $ OutOfBoundsSigned sz n
            Syntax.S16 ->
              if 0 <= n && n <= fromIntegral (maxBound::Int16)
              then
                pure $
                CheckResult
                { crExpr = IR.Int16 (fromIntegral n)
                , crKindSols = mempty
                , crTypeSols = mempty
                }
              else throwError $ OutOfBoundsSigned sz n
            Syntax.S32 ->
              if 0 <= n && n <= fromIntegral (maxBound::Int32)
              then
                pure $
                CheckResult
                { crExpr = IR.Int32 (fromIntegral n)
                , crKindSols = mempty
                , crTypeSols = mempty
                }
              else throwError $ OutOfBoundsSigned sz n
            Syntax.S64 ->
              if 0 <= n && n <= fromIntegral (maxBound::Int64)
              then
                pure $
                CheckResult
                { crExpr = IR.Int64 (fromIntegral n)
                , crKindSols = mempty
                , crTypeSols = mempty
                }
              else throwError $ OutOfBoundsUnsigned sz n
        _ -> throwError $ NotNumeric (tyNames <$> ty)
    _ -> do
      exprResult <- inferExpr tyScope letScope tyNames tmNames kinds types expr
      subs <- unifyType tyNames kinds ty (irType exprResult)
      pure $
        CheckResult
        { crExpr = applyTSubs_Expr subs $ irExpr exprResult
        , crKindSols = irKindSols exprResult
        , crTypeSols = composeTSubs subs (irTypeSols exprResult)
        }

zonkExprTypes ::
  Monad m =>
  IR.Expr (Either TMeta ty) tm ->
  m (IR.Expr ty tm)
zonkExprTypes e =
  case e of
    IR.Var a -> pure $ IR.Var a
    IR.Name n -> pure $ IR.Name n
    IR.Let bs rest -> IR.Let <$> (traverse.traverse) zonkExprTypes bs <*> zonkExprTypes rest
    IR.Inst n args ->
      IR.Inst n <$>
      (traverse.traverse)
        (either (error . ("zonking found: " <>) . show) pure)
      args
    IR.Call f args -> IR.Call <$> zonkExprTypes f <*> traverse zonkExprTypes args
    IR.UInt8 n -> pure $ IR.UInt8 n
    IR.UInt16 n -> pure $ IR.UInt16 n
    IR.UInt32 n -> pure $ IR.UInt32 n
    IR.UInt64 n -> pure $ IR.UInt64 n
    IR.Int8 n -> pure $ IR.Int8 n
    IR.Int16 n -> pure $ IR.Int16 n
    IR.Int32 n -> pure $ IR.Int32 n
    IR.Int64 n -> pure $ IR.Int64 n
    IR.BTrue -> pure $ IR.BTrue
    IR.BFalse -> pure $ IR.BFalse
    IR.New a -> IR.New <$> zonkExprTypes a
    IR.Deref a -> IR.Deref <$> zonkExprTypes a

sizeConstraintFor ::
  Int ->
  Kind ->
  IR.Constraint (Var () ty)
sizeConstraintFor nn = go nn [] (B ())
  where
    go ::
      Int ->
      [x] ->
      x ->
      Kind ->
      IR.Constraint x
    go n quants x k =
      case k of
        KType ->
          IR.CSized $
          foldl
            (\acc v -> Syntax.TApp acc $ Syntax.TVar v)
            (Syntax.TVar x)
            quants
        KArr a b ->
          IR.CForall (Text.pack $ "t" <> show n) a $
          IR.CImplies (sizeConstraintFor (n+1) a) $
          go (n+1) (fmap F quants ++ [B ()]) (F x) b
        KVar{} -> error "KVar in sizeConstraintFor"

checkFunctionBody ::
  (MonadState TCState m, MonadError TypeError m, Ord ty) =>
  Map Text (TypeScheme Void) ->
  (ty -> Text) ->
  (tm -> Text) ->
  (ty -> Kind) ->
  (tm -> TypeM ty) ->
  Text ->
  (TypeScheme ty -> TypeScheme Void) ->
  Vector (Type ty) ->
  Syntax.FunctionBody ty tm ->
  m (IR.FunctionBody ty tm, Map KMeta Kind)
checkFunctionBody tyScope tyNames argNames kinds types name mkScheme args fb =
  case fb of
    Syntax.Forall tyName rest -> do
      meta <- freshKMeta
      (rest', ksols) <-
        checkFunctionBody
          tyScope
          (unvar (\() -> tyName) tyNames)
          argNames
          (unvar (\() -> KVar meta) kinds)
          (fmap F . types)
          name
          (mkScheme . IR.SForall tyName (KVar meta))
          ((fmap.fmap) F args)
          rest
      case Map.lookup meta ksols of
        Nothing -> error $ "unsolved: " <> show meta
        Just k ->
          pure
            ( IR.Forall tyName k $
              IR.Constraint (sizeConstraintFor 0 k) $
              rest'
            , ksols
            )
    Syntax.Arg argName argTy rest -> do
      (rest', ksols) <-
        checkFunctionBody
          tyScope
          tyNames
          (unvar (\() -> argName) argNames)
          kinds
          (unvar (\() -> TypeM $ Right <$> argTy) types)
          name
          mkScheme
          (Vector.snoc args argTy)
          rest
      pure (IR.Arg argName argTy rest', ksols)
    Syntax.Done retTy expr -> do
      exprResult <-
        checkExpr
          (Map.insert name (mkScheme $ IR.SDone mempty args retTy) tyScope) -- for recursive calls
          mempty
          tyNames
          argNames
          kinds
          types
          expr
          (TypeM $ Right <$> retTy)
      expr' <- zonkExprTypes (crExpr exprResult)
      pure (IR.Done retTy expr', crKindSols exprResult)

checkFunction ::
  MonadError TypeError m =>
  Map Text (TypeScheme Void) ->
  Syntax.Function ->
  m IR.Function
checkFunction tyScope (Syntax.Function name body) =
  flip evalStateT emptyTCState $ do
    (body', _) <-
      checkFunctionBody
        tyScope
        absurd
        absurd
        absurd
        absurd
        name
        id
        mempty
        body
    pure $ IR.Function name body'
