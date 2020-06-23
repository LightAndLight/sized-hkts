{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language RankNTypes #-}
module Unify.Type (unifyType) where

import Control.Lens.Getter ((^.))
import Control.Lens.Lens (Lens')
import Control.Lens.Setter ((%=))
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State.Strict (MonadState)
import Data.Foldable (traverse_)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Vector as Vector

import Check.Kind (inferKind)
import Error.TypeError (TypeError(..), typeMismatch, renderTyName)
import Syntax (Span, TypeM, pattern TypeM, unTypeM, tmetaSpan, typemSpan)
import qualified Syntax
import IR (Kind(..))
import Unify.KMeta (HasKindMetas)
import Unify.Kind (unifyKind)
import Unify.TMeta (HasTypeMetas, getTMeta, tmetaSolutions)

unifyType ::
  ( MonadState (s ty) m, HasTypeMetas s, HasKindMetas (s ty)
  , MonadError TypeError m
  , Eq ty
  ) =>
  Map Text Kind ->
  Lens' ty Span ->
  (ty -> Either Int Text) ->
  (ty -> Kind) ->
  TypeM ty ->
  TypeM ty ->
  m ()
unifyType kindScope spans tyNames kinds expected actual = do
  eKind <- inferKind kindScope kinds expected
  aKind <- inferKind kindScope kinds actual
  unifyKind (actual ^. typemSpan spans) eKind aKind
  case unTypeM expected of
    Syntax.TVar (Left m) -> solveLeft m actual
    Syntax.TVar (Right a) ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TVar (Right b) ->
          if a == b
          then pure mempty
          else throwError $ typeMismatch tyNames (b ^. spans) expected actual
        _ -> throwError $ typeMismatch tyNames (actual ^. typemSpan spans) expected actual
    Syntax.TApp _ a b ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TApp _ a' b' -> do
          unifyType kindScope spans tyNames kinds (TypeM a) (TypeM a')
          unifyType kindScope spans tyNames kinds (TypeM b) (TypeM b')
        _ -> throwError $ typeMismatch tyNames (actual ^. typemSpan spans) expected actual
    Syntax.TInt32{} ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TInt32{} -> pure mempty
        _ -> throwError $ typeMismatch tyNames (actual ^. typemSpan spans) expected actual
    Syntax.TBool{} ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TBool{} -> pure mempty
        _ -> throwError $ typeMismatch tyNames (actual ^. typemSpan spans) expected actual
    Syntax.TPtr{} ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TPtr{} -> pure mempty
        _ -> throwError $ typeMismatch tyNames (actual ^. typemSpan spans) expected actual
    Syntax.TFun _ args ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TFun _ args' | Vector.length args == Vector.length args' ->
          traverse_
            (\(a, b) -> unifyType kindScope spans tyNames kinds (TypeM a) (TypeM b))
            (Vector.zip args args')
        _ -> throwError $ typeMismatch tyNames (actual ^. typemSpan spans) expected actual
    Syntax.TName _ n ->
      case unTypeM actual of
        Syntax.TVar (Left m) -> solveRight expected m
        Syntax.TName _ n' | n == n' -> pure mempty
        _ -> throwError $ typeMismatch tyNames (actual ^. typemSpan spans) expected actual
  where
    solveLeft m actual' = do
      m_t <- getTMeta m
      case m_t of
        Just t -> unifyType kindScope spans tyNames kinds t actual'
        Nothing ->
          case unTypeM actual' of
            Syntax.TVar (Left m') | m == m' -> pure mempty
            _ ->
              if any (either (== m) (const False)) (unTypeM actual')
              then throwError $ TypeOccurs (actual' ^. typemSpan spans) m (renderTyName . tyNames <$> actual')
              else tmetaSolutions %= Map.insert m actual'
    solveRight expected' m = do
      m_t <- getTMeta m
      case m_t of
        Just t -> unifyType kindScope spans tyNames kinds expected' t
        Nothing ->
          case unTypeM expected' of
            Syntax.TVar (Left m') | m == m' -> pure mempty
            _ ->
              if any (either (== m) (const False)) (unTypeM expected')
              then throwError $ TypeOccurs (tmetaSpan m) m (renderTyName . tyNames <$> expected')
              else tmetaSolutions %= Map.insert m expected'
