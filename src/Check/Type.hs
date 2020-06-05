{-# language BangPatterns #-}
{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language QuantifiedConstraints #-}
{-# language TemplateHaskell #-}
{-# language ViewPatterns #-}
module Check.Type
  ( CheckResult(..), InferResult(..)
  , checkExpr, inferExpr
  , HasConstraints(..)
  , applyTSubs_Constraint
  , zonkExprTypes
  )
where

import Bound.Var (unvar)
import Control.Lens.Lens (Lens')
import Control.Lens.Setter ((<>=))
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState)
import Data.Bitraversable (bitraverse)
import Data.Foldable (foldlM, foldl')
import Data.Int (Int32)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Void (Void, absurd)

import Check.Datatype (HasDatatypeFields, HasDatatypeCtors, getConstructor, getFieldType)
import Error.TypeError (TypeError(..))
import Syntax (TMeta, TypeM, pattern TypeM, unTypeM)
import qualified Syntax
import IR (Kind(..), TypeScheme)
import qualified IR
import Unify.KMeta (HasKindMetas)
import Unify.TMeta (HasTypeMetas, freshTMeta, solveTMetas_Type)
import Unify.Type (unifyType)

class HasConstraints s where
  requiredConstraints :: Lens' (s ty) (Set (IR.Constraint (Either TMeta ty)))

applyTSubs_Constraint ::
  Map TMeta (TypeM ty) ->
  IR.Constraint (Either TMeta ty) ->
  IR.Constraint (Either TMeta ty)
applyTSubs_Constraint subs =
  IR.bindConstraint (either (\m -> maybe (pure $ Left m) unTypeM $ Map.lookup m subs) (pure . Right))


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
        (Syntax.TFun $ fmap placeMetas . snd <$> args)
        (placeMetas <$> retTy)
    )

inferPattern ::
  ( MonadState (s ty) m
  , HasTypeMetas s, HasKindMetas (s ty), HasConstraints s
  , forall x. HasDatatypeFields (s x), forall x. HasDatatypeCtors (s x)
  , MonadError TypeError m
  , Ord ty
  ) =>
  Text ->
  Vector Text ->
  m (Vector (TypeM ty), TypeM ty)
inferPattern ctorName argNames = do
  ctor <- getConstructor ctorName
  let
    expectedLength = length $ IR.ctorArgs ctor
    actualLength = length argNames
  case expectedLength == actualLength of
    False -> throwError $ CtorArityMismatch ctorName expectedLength actualLength
    True -> do
      tyArgs <- traverse (\_ -> freshTMeta KType) $ IR.ctorTyArgs ctor
      let inst = fmap $ unvar (Left . (tyArgs Vector.!)) absurd
      pure
        ( TypeM . inst . snd <$> IR.ctorArgs ctor
        , TypeM . inst $ IR.ctorRetTy ctor
        )

inferExpr ::
  ( MonadState (s ty) m
  , HasTypeMetas s, HasKindMetas (s ty), HasConstraints s
  , forall x. HasDatatypeFields (s x), forall x. HasDatatypeCtors (s x)
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

    Syntax.Number n -> do
      if 0 <= n && n <= fromIntegral (maxBound::Int32)
      then
        pure $
        InferResult
        { irExpr = IR.Int32 (fromIntegral n)
        , irType = TypeM Syntax.TInt32
        }
      else throwError $ OutOfBoundsInt32 n

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

    Syntax.Project a field -> do
      aResult <- inferExpr kindScope tyScope letScope tyNames tmNames kinds types a
      aTy <- solveTMetas_Type id . unTypeM $ irType aResult
      let (t, ts) = Syntax.unApply aTy
      case t of
        Syntax.TName n -> do
          let field' = IR.parseProjection field
          m_fieldType <- getFieldType n field'
          case m_fieldType of
            Nothing -> throwError $ Doesn'tHaveField (tyNames <$> TypeM aTy) field
            Just fieldType ->
              let
                fieldType' = fieldType >>= unvar (ts !!) absurd
              in
                pure $
                InferResult
                { irExpr = IR.Project (irExpr aResult) field'
                , irType = TypeM fieldType'
                }
        _ -> throwError $ Can'tInfer (tmNames <$> expr)

    Syntax.Match a cases -> do
      aResult <- inferExpr kindScope tyScope letScope tyNames tmNames kinds types a
      resTy <- Syntax.TVar . Left <$> freshTMeta KType
      caseExprs <-
        traverse
           (\(Syntax.Case ctorName ctorArgs body) -> do
              (ctorArgTypes, patternType) <- inferPattern ctorName ctorArgs
              unifyType
                kindScope
                (Right . tyNames)
                kinds
                (irType aResult)
                patternType
              bodyResult <-
                inferExpr
                  kindScope
                  tyScope
                  letScope
                  tyNames
                  (unvar (ctorArgs Vector.!) tmNames)
                  kinds
                  (unvar (ctorArgTypes Vector.!) types)
                  body
              unifyType
                kindScope
                (Right . tyNames)
                kinds
                (TypeM resTy)
                (irType bodyResult)
              pure $ IR.Case ctorName ctorArgs (irExpr bodyResult)
           )
           cases
      pure $
        InferResult
        { irExpr = IR.Match (irExpr aResult) caseExprs
        , irType = TypeM resTy
        }

data CheckResult ty tm
  = CheckResult
  { crExpr :: IR.Expr (Either TMeta ty) tm
  }

checkExpr ::
  ( MonadState (s ty) m
  , HasTypeMetas s, HasKindMetas (s ty), HasConstraints s
  , forall x. HasDatatypeFields (s x), forall x. HasDatatypeCtors (s x)
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
checkExpr kindScope tyScope letScope tyNames tmNames kinds types expr ty = do
  exprResult <- inferExpr kindScope tyScope letScope tyNames tmNames kinds types expr
  unifyType kindScope (Right . tyNames) kinds ty (irType exprResult)
  pure $
    CheckResult
    { crExpr = irExpr exprResult
    }

zonkCaseTypes ::
  Monad m =>
  IR.Case (Either TMeta ty) tm ->
  m (IR.Case ty tm)
zonkCaseTypes (IR.Case n as e) = IR.Case n as <$> zonkExprTypes e

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
    IR.Int32 n -> pure $ IR.Int32 n
    IR.BTrue -> pure $ IR.BTrue
    IR.BFalse -> pure $ IR.BFalse
    IR.New a t ->
      IR.New <$>
      zonkExprTypes a <*>
      traverse
        (either (error . ("zonking found: " <>) . show) pure)
        t
    IR.Deref a -> IR.Deref <$> zonkExprTypes a
    IR.Project a b -> (\a' -> IR.Project a' b) <$> zonkExprTypes a
    IR.Match a bs ->
      IR.Match <$>
      zonkExprTypes a <*>
      traverse zonkCaseTypes bs
