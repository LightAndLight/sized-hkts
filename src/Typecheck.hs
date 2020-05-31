{-# language BangPatterns #-}
{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
{-# language ViewPatterns #-}
module Typecheck
  ( sizeConstraintFor
  , applyTSubs_Constraint
  , renderTyName
  , unifyType
  , TypeError(..)
  , CheckResult(..), InferResult(..)
  , checkExpr
  , inferExpr
  , zonkExprTypes
  )
where

import Bound.Var (unvar)
import Control.Lens.Setter ((%=), (<>=))
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState)
import Data.Bitraversable (bitraverse)
import Data.Foldable (foldlM, foldl', traverse_)
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

import Check.Kind (inferKind, unifyKind)
import Check.TypeError (TypeError(..))
import qualified Syntax
import IR (Kind(..), TypeScheme)
import qualified IR
import Size (sizeConstraintFor)
import TCState
  ( TMeta
  , TypeM, pattern TypeM, unTypeM
  , HasKindMetas, HasTypeMetas, HasConstraints
  , tmetaSolutions
  , getTMeta
  , freshTMeta
  , requiredConstraints
  )

applyTSubs_Constraint ::
  Map TMeta (TypeM ty) ->
  IR.Constraint (Either TMeta ty) ->
  IR.Constraint (Either TMeta ty)
applyTSubs_Constraint subs =
  IR.bindConstraint (either (\m -> maybe (pure $ Left m) unTypeM $ Map.lookup m subs) (pure . Right))

renderTyName :: Either Int Text -> Text
renderTyName = either (Text.pack . ("#" <>) . show) id

typeMismatch :: (ty -> Either Int Text) -> TypeM ty -> TypeM ty -> TypeError
typeMismatch tyNames expected actual =
  TypeMismatch (renderTyName . tyNames <$> expected) (renderTyName . tyNames <$> actual)

unifyType ::
  ( MonadState (s ty) m, HasTypeMetas s, HasKindMetas (s ty)
  , MonadError TypeError m
  , Eq ty
  ) =>
  Map Text Kind ->
  (ty -> Either Int Text) ->
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
          else throwError $ typeMismatch tyNames expected actual
        _ -> throwError $ typeMismatch tyNames expected actual
    Syntax.TApp a b ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TApp a' b' -> do
          unifyType kindScope tyNames kinds (TypeM a) (TypeM a')
          unifyType kindScope tyNames kinds (TypeM b) (TypeM b')
        _ -> throwError $ typeMismatch tyNames expected actual
    Syntax.TUInt sz ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TUInt sz' | sz == sz' -> pure mempty
        _ -> throwError $ typeMismatch tyNames expected actual
    Syntax.TInt sz ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TInt sz' | sz == sz' -> pure mempty
        _ -> throwError $ typeMismatch tyNames expected actual
    Syntax.TBool ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TBool -> pure mempty
        _ -> throwError $ typeMismatch tyNames expected actual
    Syntax.TPtr ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TPtr -> pure mempty
        _ -> throwError $ typeMismatch tyNames expected actual
    Syntax.TFun args ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TFun args' | Vector.length args == Vector.length args' ->
          traverse_
            (\(a, b) -> unifyType kindScope tyNames kinds (TypeM a) (TypeM b))
            (Vector.zip args args')
        _ -> throwError $ typeMismatch tyNames expected actual
    Syntax.TName n ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TName n' | n == n' -> pure mempty
        _ -> throwError $ typeMismatch tyNames expected actual
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
              then throwError $ TypeOccurs m (renderTyName . tyNames <$> actual')
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
              then throwError $ TypeOccurs m (renderTyName . tyNames <$> expected')
              else tmetaSolutions %= Map.insert m expected'

data InferResult ty tm
  = InferResult
  { irExpr :: IR.Expr (Either TMeta ty) tm
  , irType :: TypeM ty
  }

instantiateScheme ::
  (MonadState (s ty) m, HasTypeMetas s, Ord ty) =>
  TypeScheme Void ->
  m
    ( IR.Origin
    , Vector TMeta
    , Set (IR.Constraint (Either TMeta ty))
    , TypeM ty
    )
instantiateScheme (IR.TypeScheme origin tyArgs constraints args retTy) = do
  tyArgMetas <- traverse (\(_, k) -> freshTMeta k) tyArgs
  let placeMetas = unvar (Left . (tyArgMetas Vector.!)) absurd
  pure
    ( origin
    , tyArgMetas
    , foldl'
        (\acc c -> Set.insert (placeMetas <$> c) acc)
        mempty
        constraints
    , TypeM $
      Syntax.TApp
        (Syntax.TFun $ fmap placeMetas . snd <$> args
        )
        (placeMetas <$> retTy)
    )

inferExpr ::
  ( MonadState (s ty) m
  , HasTypeMetas s, HasKindMetas (s ty), HasConstraints s
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
      }

    Syntax.Name name -> do
      case Map.lookup name letScope of
        Nothing ->
          case Map.lookup name tyScope of
            Nothing -> throwError $ NotInScope name
            Just scheme -> do
              (origin, metas, constraints, bodyTy) <- instantiateScheme scheme
              requiredConstraints <>= constraints
              case origin of
                IR.OFunction ->
                  pure $
                    InferResult
                    { irExpr = IR.Inst name $ Syntax.TVar . Left <$> metas
                    , irType = bodyTy
                    }
                IR.OConstructor ->
                  pure $
                    InferResult
                    { irExpr = IR.Ctor name $ Syntax.TVar . Left <$> metas
                    , irType = bodyTy
                    }
                IR.ODatatype -> error "got ODatatype"
        Just ty ->
          pure $
            InferResult
            { irExpr = IR.Name name
            , irType = ty
            }

    Syntax.Let bindings body -> do
      (letScope', bindings') <-
        foldlM
          (\(acc, bs) (n, b) -> do
             bResult <- inferExpr kindScope tyScope acc tyNames tmNames kinds types b
             requiredConstraints <>= Set.singleton (IR.CSized . unTypeM $ irType bResult)
             pure
               ( Map.insert n (irType bResult) acc
               , Vector.snoc bs ((n, irExpr bResult), unTypeM $ irType bResult)
               )
          )
          (mempty, mempty)
          bindings
      bodyResult <- inferExpr kindScope tyScope letScope' tyNames tmNames kinds types body
      pure $
        InferResult
        { irExpr = IR.Let bindings' $ irExpr bodyResult
        , irType = irType bodyResult
        }

    Syntax.Call fun args -> do
      funResult <- inferExpr kindScope tyScope letScope tyNames tmNames kinds types fun
      (args', argTys) <-
        foldlM
          (\(as, atys) arg -> do
             argResult <- inferExpr kindScope tyScope letScope tyNames tmNames kinds types arg
             pure
               ( Vector.snoc as $ irExpr argResult
               , Vector.snoc atys . unTypeM $ irType argResult
               )
          )
          (mempty, mempty)
          args
      retTy <- Syntax.TVar . Left <$> freshTMeta KType
      unifyType
        kindScope
        (Right . tyNames)
        kinds
        (TypeM $ Syntax.TApp (Syntax.TFun argTys) retTy)
        (irType funResult)
      pure $
        InferResult
        { irExpr = IR.Call (irExpr funResult) args' retTy
        , irType = TypeM retTy
        }

    Syntax.Number{} -> throwError $ Can'tInfer (tmNames <$> expr)

    Syntax.BTrue ->
      pure $
      InferResult
      { irExpr = IR.BTrue
      , irType = TypeM Syntax.TBool
      }

    Syntax.BFalse ->
      pure $
      InferResult
      { irExpr = IR.BFalse
      , irType = TypeM Syntax.TBool
      }

    Syntax.New a -> do
      aResult <- inferExpr kindScope tyScope letScope tyNames tmNames kinds types a
      requiredConstraints <>= Set.singleton (IR.CSized . unTypeM $ irType aResult)
      pure $
        InferResult
        { irExpr = IR.New (irExpr aResult) (unTypeM $ irType aResult)
        , irType = TypeM $ Syntax.TApp Syntax.TPtr (unTypeM $ irType aResult)
        }

    Syntax.Deref a -> do
      aResult <- inferExpr kindScope tyScope letScope tyNames tmNames kinds types a
      meta <- freshTMeta KType
      unifyType
        kindScope
        (Right . tyNames)
        kinds
        (TypeM $ Syntax.TApp Syntax.TPtr $ Syntax.TVar $ Left meta)
        (irType aResult)
      pure $
        InferResult
        { irExpr = IR.Deref $ irExpr aResult
        , irType = TypeM $ Syntax.TVar (Left meta)
        }

data CheckResult ty tm
  = CheckResult
  { crExpr :: IR.Expr (Either TMeta ty) tm
  }

checkExpr ::
  ( MonadState (s ty) m
  , HasTypeMetas s, HasKindMetas (s ty), HasConstraints s
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
    Syntax.Number n -> do
      case unTypeM ty of
        Syntax.TVar (Left m) -> do
          m_ty' <- getTMeta m
          case m_ty' of
            Nothing -> throwError $ NotNumeric (tyNames <$> ty)
            Just ty' ->
              checkExpr
                kindScope
                tyScope
                letScope
                tyNames
                tmNames
                kinds
                types
                expr
                ty'
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
    Syntax.New a -> do
      aTy <- Syntax.TVar . Left <$> freshTMeta KType
      let expected = Syntax.TApp Syntax.TPtr aTy
      unifyType
        kindScope
        (Right . tyNames)
        kinds
        (TypeM expected)
        ty
      a' <-
        checkExpr
          kindScope
          tyScope
          letScope
          tyNames
          tmNames
          kinds
          types
          a
          (TypeM aTy)
      pure $ CheckResult { crExpr = IR.New (crExpr a') aTy }
    Syntax.Call name args -> do
      name' <-
        inferExpr
          kindScope
          tyScope
          letScope
          tyNames
          tmNames
          kinds
          types
          name
      expectedArgs <- fmap (Syntax.TVar . Left) <$> Vector.replicateM (length args) (freshTMeta KType)
      let expected = Syntax.TApp (Syntax.TFun expectedArgs) (unTypeM ty)
      unifyType kindScope (Right . tyNames) kinds (TypeM expected) (irType name')
      args' <-
        traverse
          (\(e, t) -> checkExpr kindScope tyScope letScope tyNames tmNames kinds types e (TypeM t))
          (Vector.zip args expectedArgs)
      pure $
        CheckResult
        { crExpr =
          IR.Call (irExpr name') (crExpr <$> args') (unTypeM ty)
        }
    Syntax.Let bindings rest -> do
      bindingTypes <-
        foldlM
          (\acc (n, _) -> do
             m <- freshTMeta KType
             pure $ Map.insert n (TypeM . Syntax.TVar $ Left m) acc
          )
          mempty
          bindings
      rest' <-
        checkExpr
          kindScope
          tyScope
          (bindingTypes <> letScope)
          tyNames
          tmNames
          kinds
          types
          rest
          ty
      (bindings', _) <-
        foldlM
          (\(bs', letScope') (bn, be) -> do
             let bt = bindingTypes Map.! bn
             be' <-
               checkExpr
                 kindScope
                 tyScope
                 (letScope' <> letScope)
                 tyNames
                 tmNames
                 kinds
                 types
                 be
                 bt
             pure
               ( Vector.snoc bs' ((bn, crExpr be'), unTypeM bt)
               , Map.insert bn bt letScope'
               )
          )
          (mempty, mempty)
          bindings
      pure $ CheckResult { crExpr = IR.Let bindings' (crExpr rest')}
    _ -> do
      exprResult <- inferExpr kindScope tyScope letScope tyNames tmNames kinds types expr
      unifyType kindScope (Right . tyNames) kinds ty (irType exprResult)
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
    IR.Let bs rest ->
      IR.Let <$>
      traverse
        (bitraverse
           (traverse zonkExprTypes)
           (traverse (either (error . ("zonking found: " <>) . show) pure))
        )
        bs <*>
      zonkExprTypes rest
    IR.Inst n args ->
      IR.Inst n <$>
      (traverse.traverse)
        (either (error . ("zonking found: " <>) . show) pure)
      args
    IR.Ctor n ts ->
      IR.Ctor n <$>
      (traverse.traverse)
        (either (error . ("zonking found: " <>) . show) pure)
      ts
    IR.Call f args t ->
      IR.Call <$>
      zonkExprTypes f <*>
      traverse zonkExprTypes args <*>
      traverse (either (error . ("zonking found: " <>) . show) pure) t
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
    IR.New a t ->
      IR.New <$>
      zonkExprTypes a <*>
      traverse
        (either (error . ("zonking found: " <>) . show) pure)
        t
    IR.Deref a -> IR.Deref <$> zonkExprTypes a
