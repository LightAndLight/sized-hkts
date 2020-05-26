{-# language BangPatterns #-}
{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
{-# language ViewPatterns #-}
module Typecheck
  ( sizeConstraintFor
  , applyTSubs_Constraint
  , unifyType
  , TypeError(..)
  , CheckResult(..), InferResult(..)
  , checkExpr
  , inferExpr
  , checkFunction
  )
where

import Bound.Var (Var(..), unvar)
import Control.Lens.Setter ((%=), over, mapped)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, evalStateT, runStateT)
import Data.Foldable (foldlM, traverse_)
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

import Check.Kind (checkKind, inferKind, unifyKind)
import Check.TypeError (TypeError(..))
import Syntax (Type)
import qualified Syntax
import IR (Kind(..), TypeScheme)
import qualified IR
import TCState
  ( TMeta
  , TypeM, pattern TypeM, unTypeM
  , TCState, emptyTCState
  , HasKindMetas, HasTypeMetas
  , tmetaSolutions
  , getTMeta, getKMeta
  , freshTMeta, freshKMeta
  , filterTypeSolutions
  )

applyTSubs_Constraint ::
  Map TMeta (TypeM ty) ->
  IR.Constraint (Either TMeta ty) ->
  IR.Constraint (Either TMeta ty)
applyTSubs_Constraint subs =
  IR.bindConstraint (either (\m -> maybe (pure $ Left m) unTypeM $ Map.lookup m subs) (pure . Right))

unifyType ::
  ( MonadState s m, HasTypeMetas s s ty ty, HasKindMetas s
  , MonadError TypeError m
  , Eq ty
  ) =>
  Map Text Kind ->
  (ty -> Text) ->
  (ty -> Kind) ->
  TypeM ty ->
  TypeM ty ->
  m ()
unifyType kindScope tyNames kinds expected actual = do
  eKind <- inferKind kindScope kinds expected
  aKind <- inferKind kindScope kinds actual
  unifyKind eKind aKind
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
          unifyType kindScope tyNames kinds (TypeM a) (TypeM a')
          unifyType kindScope tyNames kinds (TypeM b) (TypeM b')
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
          traverse_
            (\(a, b) -> unifyType kindScope tyNames kinds (TypeM a) (TypeM b))
            (Vector.zip args args')
        _ -> throwError $ TypeMismatch (tyNames <$> expected) (tyNames <$> actual)
    Syntax.TName n ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TName n' | n == n' -> pure mempty
        _ -> throwError $ TypeMismatch (tyNames <$> expected) (tyNames <$> actual)
  where
    solveLeft m actual' = do
      m_t <- getTMeta m
      case m_t of
        Just t -> unifyType kindScope tyNames kinds t actual'
        Nothing ->
          case unTypeM actual' of
            Syntax.TVar (Left m') | m == m' -> pure mempty
            _ ->
              if any (either (== m) (const False)) (unTypeM actual')
              then throwError $ TypeOccurs m (tyNames <$> actual')
              else tmetaSolutions %= Map.insert m actual'
    solveRight expected' m = do
      m_t <- getTMeta m
      case m_t of
        Just t -> unifyType kindScope tyNames kinds expected' t
        Nothing ->
          case unTypeM expected' of
            Syntax.TVar (Left m') | m == m' -> pure mempty
            _ ->
              if any (either (== m) (const False)) (unTypeM expected')
              then throwError $ TypeOccurs m (tyNames <$> expected')
              else tmetaSolutions %= Map.insert m expected'

data InferResult ty tm
  = InferResult
  { irExpr :: IR.Expr (Either TMeta ty) tm
  , irType :: TypeM ty
  , irConstraints :: Set (IR.Constraint (Either TMeta ty))
  }

instantiateScheme ::
  (MonadState s m, HasTypeMetas s s ty ty) =>
  TypeScheme Void ->
  m ([TMeta], Vector (IR.Constraint (Either TMeta ty)), TypeM ty)
instantiateScheme = go (Right . absurd)
  where
    go ::
      (MonadState s m, HasTypeMetas s s ty ty) =>
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
  ( MonadState s m, HasTypeMetas s s ty ty, HasKindMetas s
  , MonadError TypeError m
  , Ord ty
  ) =>
  Map Text Kind ->
  Map Text (TypeScheme Void) ->
  Map Text (TypeM ty) ->
  (ty -> Text) ->
  (tm -> Text) ->
  (ty -> Kind) ->
  (tm -> TypeM ty) ->
  Syntax.Expr tm ->
  m (InferResult ty tm)
inferExpr kindScope tyScope letScope tyNames tmNames kinds types expr =
  case expr of
    Syntax.Var a ->
      pure $
      InferResult
      { irExpr = IR.Var a
      , irType = types a
      , irConstraints = mempty
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
                }
        Just ty ->
          pure $
            InferResult
            { irExpr = IR.Name name
            , irType = ty
            , irConstraints = mempty
            }

    Syntax.Let bindings body -> do
      (letScope', bindings', constraints) <-
        foldlM
          (\(acc, bs, cs) (n, b) -> do
             bResult <- inferExpr kindScope tyScope acc tyNames tmNames kinds types b
             pure
               ( Map.insert n (irType bResult) acc
               , Vector.snoc bs (n, irExpr bResult)
               , irConstraints bResult <> cs
               )
          )
          (mempty, mempty, mempty)
          bindings
      bodyResult <- inferExpr kindScope tyScope letScope' tyNames tmNames kinds types body
      pure $
        InferResult
        { irExpr = IR.Let bindings' $ irExpr bodyResult
        , irType = irType bodyResult
        , irConstraints = irConstraints bodyResult <> constraints
        }

    Syntax.Call fun args -> do
      funResult <- inferExpr kindScope tyScope letScope tyNames tmNames kinds types fun
      (args', argTys, constraints) <-
        foldlM
          (\(as, atys, cs) arg -> do
             argResult <- inferExpr kindScope tyScope letScope tyNames tmNames kinds types arg
             pure
               ( Vector.snoc as $ irExpr argResult
               , Vector.snoc atys . unTypeM $ irType argResult
               , irConstraints argResult <> cs
               )
          )
          (mempty, mempty, irConstraints funResult)
          args
      meta <- freshTMeta KType
      unifyType
        kindScope
        tyNames
        kinds
        (TypeM $ Syntax.TApp (Syntax.TFun argTys) (Syntax.TVar $ Left meta))
        (irType funResult)
      pure $
        InferResult
        { irExpr = IR.Call (irExpr funResult) args'
        , irType = TypeM . Syntax.TVar $ Left meta
        , irConstraints = constraints
        }

    Syntax.Number{} -> throwError $ Can'tInfer (tmNames <$> expr)

    Syntax.BTrue ->
      pure $
      InferResult
      { irExpr = IR.BTrue
      , irType = TypeM Syntax.TBool
      , irConstraints = mempty
      }

    Syntax.BFalse ->
      pure $
      InferResult
      { irExpr = IR.BTrue
      , irType = TypeM Syntax.TBool
      , irConstraints = mempty
      }

    Syntax.New a -> do
      aResult <- inferExpr kindScope tyScope letScope tyNames tmNames kinds types a
      pure $
        InferResult
        { irExpr = IR.New $ irExpr aResult
        , irType = TypeM $ Syntax.TApp Syntax.TPtr (unTypeM $ irType aResult)
        , irConstraints = irConstraints aResult
        }

    Syntax.Deref a -> do
      aResult <- inferExpr kindScope tyScope letScope tyNames tmNames kinds types a
      meta <- freshTMeta KType
      unifyType
        kindScope
        tyNames
        kinds
        (TypeM $ Syntax.TApp Syntax.TPtr $ Syntax.TVar $ Left meta)
        (irType aResult)
      pure $
        InferResult
        { irExpr = IR.Deref $ irExpr aResult
        , irType = TypeM $ Syntax.TVar (Left meta)
        , irConstraints = irConstraints aResult
        }

data CheckResult ty tm
  = CheckResult
  { crExpr :: IR.Expr (Either TMeta ty) tm
  }

checkExpr ::
  ( MonadState s m, HasTypeMetas s s ty ty, HasKindMetas s
  , MonadError TypeError m
  , Ord ty
  ) =>
  Map Text Kind ->
  Map Text (TypeScheme Void) ->
  Map Text (TypeM ty) ->
  (ty -> Text) ->
  (tm -> Text) ->
  (ty -> Kind) ->
  (tm -> TypeM ty) ->
  Syntax.Expr tm ->
  TypeM ty ->
  m (CheckResult ty tm)
checkExpr kindScope tyScope letScope tyNames tmNames kinds types expr ty =
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
                }
              else throwError $ OutOfBoundsUnsigned sz n
            Syntax.S16 ->
              if 0 <= n && n <= fromIntegral (maxBound::Word16)
              then
                pure $
                CheckResult
                { crExpr = IR.UInt16 (fromIntegral n)
                }
              else throwError $ OutOfBoundsUnsigned sz n
            Syntax.S32 ->
              if 0 <= n && n <= fromIntegral (maxBound::Word32)
              then
                pure $
                CheckResult
                { crExpr = IR.UInt32 (fromIntegral n)
                }
              else throwError $ OutOfBoundsUnsigned sz n
            Syntax.S64 ->
              if 0 <= n && n <= fromIntegral (maxBound::Word64)
              then
                pure $
                CheckResult
                { crExpr = IR.UInt64 (fromIntegral n)
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
                }
              else throwError $ OutOfBoundsSigned sz n
            Syntax.S16 ->
              if 0 <= n && n <= fromIntegral (maxBound::Int16)
              then
                pure $
                CheckResult
                { crExpr = IR.Int16 (fromIntegral n)
                }
              else throwError $ OutOfBoundsSigned sz n
            Syntax.S32 ->
              if 0 <= n && n <= fromIntegral (maxBound::Int32)
              then
                pure $
                CheckResult
                { crExpr = IR.Int32 (fromIntegral n)
                }
              else throwError $ OutOfBoundsSigned sz n
            Syntax.S64 ->
              if 0 <= n && n <= fromIntegral (maxBound::Int64)
              then
                pure $
                CheckResult
                { crExpr = IR.Int64 (fromIntegral n)
                }
              else throwError $ OutOfBoundsUnsigned sz n
        _ -> throwError $ NotNumeric (tyNames <$> ty)
    _ -> do
      exprResult <- inferExpr kindScope tyScope letScope tyNames tmNames kinds types expr
      unifyType kindScope tyNames kinds ty (irType exprResult)
      pure $
        CheckResult
        { crExpr = irExpr exprResult
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
  ( MonadError TypeError m
  , Ord ty
  ) =>
  TCState ty ->
  Map Text Kind ->
  Map Text (TypeScheme Void) ->
  (ty -> Text) ->
  (tm -> Text) ->
  (ty -> Kind) ->
  (tm -> TypeM ty) ->
  Text ->
  (TypeScheme ty -> TypeScheme Void) ->
  Vector (Type ty) ->
  Syntax.FunctionBody ty tm ->
  m (IR.FunctionBody ty tm, TCState ty)
checkFunctionBody tcstate kindScope tyScope tyNames argNames kinds types name mkScheme args fb =
  case fb of
    Syntax.Forall tyName rest -> do
      (meta, tcstate') <- runStateT freshKMeta tcstate
      (rest', tcstate'') <-
        checkFunctionBody
          (over (tmetaSolutions.mapped.mapped) F tcstate')
          kindScope
          tyScope
          (unvar (\() -> tyName) tyNames)
          argNames
          (unvar (\() -> KVar meta) kinds)
          (fmap F . types)
          name
          (mkScheme . IR.SForall tyName (KVar meta))
          ((fmap.fmap) F args)
          rest
      m_k <- evalStateT (getKMeta meta) tcstate''
      case m_k of
        Nothing -> error $ "unsolved: " <> show meta
        Just k ->
          pure
            ( IR.Forall tyName k $
              IR.Constraint (sizeConstraintFor 0 k) $
              rest'
            , filterTypeSolutions (unvar (\() -> Nothing) Just) tcstate''
            )
    Syntax.Arg argName argTy rest -> do
      let argTy' = TypeM $ Right <$> argTy
      ((), tcstate') <-
        flip runStateT tcstate $
        checkKind kindScope kinds argTy' KType
      (rest', tcstate'') <-
        checkFunctionBody
          tcstate'
          kindScope
          tyScope
          tyNames
          (unvar (\() -> argName) argNames)
          kinds
          (unvar (\() -> argTy') types)
          name
          mkScheme
          (Vector.snoc args argTy)
          rest
      pure (IR.Arg argName argTy rest', tcstate'')
    Syntax.Done retTy expr ->
      flip runStateT tcstate $ do
        exprResult <-
          checkExpr
            kindScope
            (Map.insert name (mkScheme $ IR.SDone mempty args retTy) tyScope) -- for recursive calls
            mempty
            tyNames
            argNames
            kinds
            types
            expr
            (TypeM $ Right <$> retTy)
        expr' <- zonkExprTypes (crExpr exprResult)
        pure (IR.Done retTy expr')

checkFunction ::
  MonadError TypeError m =>
  Map Text Kind ->
  Map Text (TypeScheme Void) ->
  Syntax.Function ->
  m IR.Function
checkFunction kindScope tyScope (Syntax.Function name body) = do
  (body', _) <-
    checkFunctionBody
      emptyTCState
      kindScope
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
