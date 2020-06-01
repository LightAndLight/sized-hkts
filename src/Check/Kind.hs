{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
module Check.Kind
  ( checkKind
  , inferKind
  , unifyKind
  )
where

import Control.Lens.Setter ((%=))
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid (Any(..))
import Data.Text (Text)

import Check.TypeError (TypeError(..))
import IR (Kind(..), foldKMeta)
import Syntax (TypeM, pattern TypeM, unTypeM)
import qualified Syntax
import TCState
  ( HasKindMetas, HasTypeMetas, kmetaSolutions
  , freshKMeta
  , getKMeta, getTMetaKind
  )

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

checkKind ::
  ( MonadState (s ty) m, HasTypeMetas s, HasKindMetas (s ty)
  , MonadError TypeError m
  ) =>
  Map Text Kind ->
  (ty -> Kind) ->
  TypeM ty ->
  Kind ->
  m ()
checkKind kindScope kinds ty k = do
  k' <- inferKind kindScope kinds ty
  unifyKind k k'

inferKind ::
  ( MonadState (s ty) m, HasTypeMetas s, HasKindMetas (s ty)
  , MonadError TypeError m
  ) =>
  Map Text Kind ->
  (ty -> Kind) ->
  TypeM ty ->
  m Kind
inferKind kindScope kinds ty =
  case unTypeM ty of
    Syntax.TVar (Left m) -> do
      mk <- getTMetaKind m
      case mk of
        Nothing -> error $ "Missing " <> show mk
        Just k -> pure k
    Syntax.TVar (Right a) -> pure $ kinds a
    Syntax.TApp a b -> do
      aK <- inferKind kindScope kinds (TypeM a)
      bK <- inferKind kindScope kinds (TypeM b)
      meta <- freshKMeta
      let expected = KArr bK (KVar meta)
      unifyKind expected aK
      pure $ KVar meta
    Syntax.TInt32 -> pure KType
    Syntax.TBool -> pure KType
    Syntax.TPtr -> pure $ KArr KType KType
    Syntax.TFun{} -> pure $ KArr KType KType
    Syntax.TName n ->
      case Map.lookup n kindScope of
        Nothing -> throwError $ TNotInScope n
        Just k -> pure k

