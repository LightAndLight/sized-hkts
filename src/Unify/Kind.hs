{-# language FlexibleContexts #-}
module Unify.Kind (unifyKind) where

import Control.Lens.Setter ((%=))
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State.Strict (MonadState)
import qualified Data.Map as Map
import Data.Monoid (Any(..))

import Error.TypeError (TypeError(..))
import IR (Kind(..), foldKMeta)
import Syntax (Span)
import Unify.KMeta (HasKindMetas, getKMeta, kmetaSolutions)

unifyKind ::
  ( MonadState s m, HasKindMetas s
  , MonadError TypeError m
  ) =>
  Span ->
  Kind ->
  Kind ->
  m ()
unifyKind sp expected actual =
  case expected of
    KVar v | KVar v' <- actual, v == v' -> pure ()
    KVar v -> solveLeft v actual
    KArr a b ->
      case actual of
        KVar v -> solveRight expected v
        KArr a' b' -> do
          unifyKind sp a a'
          unifyKind sp b b'
        _ -> throwError $ KindMismatch sp expected actual
    KType ->
      case actual of
        KVar v -> solveRight expected v
        KType -> pure ()
        _ -> throwError $ KindMismatch sp expected actual
  where
    solveLeft v k = do
      m_k' <- getKMeta v
      case m_k' of
        Nothing ->
          if getAny $ foldKMeta (Any . (v ==)) k
          then throwError $ KindOccurs sp v k
          else kmetaSolutions %= Map.insert v k
        Just k' -> unifyKind sp k' k
    solveRight k v = do
      m_k' <- getKMeta v
      case m_k' of
        Nothing ->
          if getAny $ foldKMeta (Any . (v ==)) k
          then throwError $ KindOccurs sp v k
          else kmetaSolutions %= Map.insert v k
        Just k' -> unifyKind sp k k'
