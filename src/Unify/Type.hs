{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
module Unify.Type (unifyType) where

import Control.Lens.Setter ((%=))
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState)
import Data.Foldable (traverse_)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Vector as Vector

import Check.Kind (inferKind)
import Check.TypeError (TypeError(..), typeMismatch, renderTyName)
import Syntax (TypeM, pattern TypeM, unTypeM)
import qualified Syntax
import IR (Kind(..))
import TCState
  ( HasKindMetas, HasTypeMetas
  , tmetaSolutions
  , getTMeta
  )
import Unify.Kind (unifyKind)

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
    Syntax.TInt32 ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TInt32 -> pure mempty
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
