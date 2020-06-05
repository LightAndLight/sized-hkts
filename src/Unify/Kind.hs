{-# language FlexibleContexts #-}
module Unify.Kind
  ( unifyKind
  , HasKindMetas(..)
  , freshKMeta
  , getKMeta
  , solveKMetasMaybe
  , solveKMetas
  )
where

import Control.Applicative (empty)
import Control.Lens.Getter (use)
import Control.Lens.Lens (Lens')
import Control.Lens.Setter ((%=), (.=))
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid (Any(..))

import Error.TypeError (TypeError(..))
import IR (KMeta(..), Kind(..), foldKMeta)

class HasKindMetas s where
  nextKMeta :: Lens' s KMeta
  kmetaSolutions :: Lens' s (Map KMeta Kind)

freshKMeta :: (MonadState s m, HasKindMetas s) => m KMeta
freshKMeta = do
  KMeta k <- use nextKMeta
  nextKMeta .= KMeta (k+1)
  pure $ KMeta k

getKMeta ::
  (MonadState s m, HasKindMetas s) =>
  KMeta ->
  m (Maybe Kind)
getKMeta v = do
  sols <- use kmetaSolutions
  pure $ Map.lookup v sols

solveKMetasMaybe ::
  (MonadState s m, HasKindMetas s) =>
  IR.Kind ->
  m (Maybe IR.Kind)
solveKMetasMaybe = runMaybeT . go
  where
    go ::
      (MonadState s m, HasKindMetas s) =>
      IR.Kind ->
      MaybeT m IR.Kind
    go k =
      case k of
        IR.KVar m ->
          maybe empty go =<<
          lift (getKMeta m)
        IR.KArr a b ->
          IR.KArr <$> go a <*> go b
        IR.KType -> pure IR.KType

solveKMetas ::
  (MonadState s m, HasKindMetas s) =>
  IR.Kind ->
  m IR.Kind
solveKMetas = go
  where
    go ::
      (MonadState s m, HasKindMetas s) =>
      IR.Kind ->
      m IR.Kind
    go k =
      case k of
        IR.KVar m ->
          maybe (pure $ IR.KVar m) go =<<
          getKMeta m
        IR.KArr a b ->
          IR.KArr <$> go a <*> go b
        IR.KType -> pure IR.KType


unifyKind ::
  ( MonadState s m, HasKindMetas s
  , MonadError TypeError m
  ) =>
  Kind ->
  Kind ->
  m ()
unifyKind expected actual =
  case expected of
    KVar v | KVar v' <- actual, v == v' -> pure ()
    KVar v -> solveLeft v actual
    KArr a b ->
      case actual of
        KVar v -> solveRight expected v
        KArr a' b' -> do
          unifyKind a a'
          unifyKind b b'
        _ -> throwError $ KindMismatch expected actual
    KType ->
      case actual of
        KVar v -> solveRight expected v
        KType -> pure ()
        _ -> throwError $ KindMismatch expected actual
  where
    solveLeft v k = do
      m_k' <- getKMeta v
      case m_k' of
        Nothing ->
          if getAny $ foldKMeta (Any . (v ==)) k
          then throwError $ KindOccurs v k
          else kmetaSolutions %= Map.insert v k
        Just k' -> unifyKind k' k
    solveRight k v = do
      m_k' <- getKMeta v
      case m_k' of
        Nothing ->
          if getAny $ foldKMeta (Any . (v ==)) k
          then throwError $ KindOccurs v k
          else kmetaSolutions %= Map.insert v k
        Just k' -> unifyKind k k'
