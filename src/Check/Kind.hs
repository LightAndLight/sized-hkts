{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
module Check.Kind
  ( checkKind
  , inferKind
  )
where

import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State.Strict (MonadState)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)

import Error.TypeError (TypeError(..))
import IR (Kind(..))
import Syntax (TypeM, pattern TypeM, unTypeM)
import qualified Syntax
import Unify.KMeta (HasKindMetas, freshKMeta)
import Unify.Kind (unifyKind)
import Unify.TMeta (HasTypeMetas, getTMetaKind)

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

