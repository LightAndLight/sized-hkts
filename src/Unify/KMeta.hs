module Unify.KMeta
  ( HasKindMetas(..)
  , freshKMeta
  , getKMeta
  , solveKMetasMaybe
  , solveKMetas
  )
where

import Control.Applicative (empty)
import Control.Lens.Getter (use)
import Control.Lens.Lens (Lens')
import Control.Lens.Setter ((.=))
import Control.Monad.State.Strict (MonadState)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import Data.Map (Map)
import qualified Data.Map as Map

import IR (KMeta(..), Kind(..))

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
