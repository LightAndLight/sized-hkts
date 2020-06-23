{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language RankNTypes #-}
module Check.Kind
  ( checkKind
  , inferKind
  )
where

import Control.Lens.Getter ((^.))
import Control.Lens.Lens (Lens')
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State.Strict (MonadState)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)

import Error.TypeError (TypeError(..))
import IR (Kind(..))
import Syntax (Span, TypeM, pattern TypeM, unTypeM, typemSpan)
import qualified Syntax
import Unify.KMeta (HasKindMetas, freshKMeta)
import Unify.Kind (unifyKind)
import Unify.TMeta (HasTypeMetas, getTMetaKind)

checkKind ::
  ( MonadState (s ty) m, HasTypeMetas s, HasKindMetas (s ty)
  , MonadError TypeError m
  ) =>
  Map Text Kind ->
  Lens' ty Span ->
  (ty -> Kind) ->
  TypeM ty ->
  Kind ->
  m ()
checkKind kindScope spans kinds ty k = do
  k' <- inferKind kindScope kinds ty
  let sp = ty ^. typemSpan spans
  unifyKind sp k k'

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
    Syntax.TApp sp a b -> do
      aK <- inferKind kindScope kinds (TypeM a)
      bK <- inferKind kindScope kinds (TypeM b)
      meta <- freshKMeta
      let expected = KArr bK (KVar meta)
      unifyKind sp expected aK
      pure $ KVar meta
    Syntax.TInt32{} -> pure KType
    Syntax.TBool{} -> pure KType
    Syntax.TPtr{} -> pure $ KArr KType KType
    Syntax.TFun{} -> pure $ KArr KType KType
    Syntax.TName sp n ->
      case Map.lookup n kindScope of
        Nothing -> throwError $ TNotInScope sp
        Just k -> pure k

