{-# language DeriveFunctor #-}
{-# language FlexibleInstances #-}
{-# language FunctionalDependencies, MultiParamTypeClasses, TypeFamilies #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
module TCState
  ( TMeta(..), TypeM, pattern TypeM, unTypeM
  , TCState
  , emptyTCState
  , HasTypeMetas(..), HasKindMetas(..)
  , filterTypeSolutions
  , freshTMeta, freshKMeta
  , getTMeta, getKMeta
  , getTMetaKind
  , solveKMetas
  , solveTMetas_Expr
  , solveMetas_Constraint
  )
where

import Bound.Var (Var(..))
import Control.Lens.Getter ((^.), use)
import Control.Lens.Lens (Lens, Lens')
import Control.Lens.Setter ((.~), (%=), (.=))
import Control.Lens.TH (makeLenses)
import Control.Monad.Except (ExceptT(..), runExceptT)
import Control.Monad.State (MonadState)
import Data.Foldable (foldl')
import Data.Function ((&))
import Data.Map (Map)
import qualified Data.Map as Map

import IR (KMeta(..), Kind(..))
import qualified IR
import Syntax (Type(..))

newtype TMeta = TMeta Int
  deriving (Eq, Ord, Show)

type TypeM = ExceptT TMeta Type

pattern TypeM :: Type (Either TMeta ty) -> TypeM ty
pattern TypeM a = ExceptT a

unTypeM :: TypeM ty -> Type (Either TMeta ty)
unTypeM = runExceptT


data TCState ty
  = TCState
  { _tcsKindMeta :: KMeta
  , _tcsKindSolutions :: Map KMeta Kind
  , _tcsTypeMeta :: TMeta
  , _tcsTypeMetaKinds :: Map TMeta Kind
  , _tcsTypeSolutions :: Map TMeta (TypeM ty)
  }
makeLenses ''TCState

emptyTCState :: TCState ty
emptyTCState =
  TCState
  { _tcsKindMeta = KMeta 0
  , _tcsKindSolutions = mempty
  , _tcsTypeMeta = TMeta 0
  , _tcsTypeMetaKinds = mempty
  , _tcsTypeSolutions = mempty
  }

class HasTypeMetas s t ty ty' | s -> ty, t -> ty', s ty' -> t, t ty -> ty' where
  nextTMeta :: (s ~ t) => Lens s t TMeta TMeta
  tmetaKinds :: (s ~ t) => Lens s t (Map TMeta Kind) (Map TMeta Kind)
  tmetaSolutions :: Lens s t (Map TMeta (TypeM ty)) (Map TMeta (TypeM ty'))

instance HasTypeMetas (TCState ty) (TCState ty') ty ty' where
  nextTMeta = tcsTypeMeta
  tmetaKinds = tcsTypeMetaKinds
  tmetaSolutions = tcsTypeSolutions

class HasKindMetas s where
  nextKMeta :: Lens' s KMeta
  kmetaSolutions :: Lens' s (Map KMeta Kind)

instance HasKindMetas (TCState ty) where
  nextKMeta = tcsKindMeta
  kmetaSolutions = tcsKindSolutions

filterTypeSolutions :: (HasTypeMetas s s a a, HasTypeMetas s t a b) => (a -> Maybe b) -> s -> t
filterTypeSolutions f tcs =
  let
    (tmetas, sols') =
      Map.foldrWithKey
        (\k a (ms, ss) ->
           case traverse f a of
             Nothing -> (k:ms, ss)
             Just a' -> (ms, Map.insert k a' ss)
        )
        ([], mempty)
        (tcs ^. tmetaSolutions)
    kinds' = foldl' (flip Map.delete) (tcs ^. tmetaKinds) tmetas
  in
    tcs &
    tmetaKinds .~ kinds' &
    tmetaSolutions .~ sols'

freshKMeta :: (MonadState s m, HasKindMetas s) => m KMeta
freshKMeta = do
  KMeta k <- use nextKMeta
  nextKMeta .= KMeta (k+1)
  pure $ KMeta k

freshTMeta :: (MonadState s m, HasTypeMetas s s ty ty) => Kind -> m TMeta
freshTMeta k = do
  TMeta t <- use nextTMeta
  nextTMeta .= TMeta (t+1)
  tmetaKinds %= Map.insert (TMeta t) k
  pure $ TMeta t

getKMeta ::
  (MonadState s m, HasKindMetas s) =>
  KMeta ->
  m (Maybe Kind)
getKMeta v = do
  sols <- use kmetaSolutions
  pure $ Map.lookup v sols

getTMeta ::
  (MonadState s m, HasTypeMetas s s ty ty) =>
  TMeta ->
  m (Maybe (TypeM ty))
getTMeta v = do
  sols <- use tmetaSolutions
  pure $ Map.lookup v sols

getTMetaKind :: (MonadState s m, HasTypeMetas s s ty ty) => TMeta -> m (Maybe Kind)
getTMetaKind v = do
  ks <- use tmetaKinds
  pure $ Map.lookup v ks

solveTMetas_Type ::
  (MonadState s m, HasTypeMetas s s ty ty) =>
  (ty -> a) ->
  Type (Either TMeta a) ->
  m (Type (Either TMeta a))
solveTMetas_Type d = go d
  where
    go ::
      (MonadState s m, HasTypeMetas s s ty ty) =>
      (ty -> a) ->
      Type (Either TMeta a) ->
      m (Type (Either TMeta a))
    go depth t =
      case t of
        TVar a ->
          case a of
            Left m ->
              getTMeta m >>=
              maybe
                (pure $ TVar $ Left m)
                (go depth . unTypeM . fmap depth)
            Right x -> pure $ TVar $ Right x
        TApp a b -> TApp <$> go depth a <*> go depth b
        TUInt sz -> pure $ TUInt sz
        TInt sz -> pure $ TInt sz
        TBool -> pure TBool
        TPtr -> pure TPtr
        TFun ts -> TFun <$> traverse (go depth) ts
        TName n -> pure $ TName n

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

solveMetas_Constraint ::
  (MonadState s m, HasTypeMetas s s ty ty, HasKindMetas s) =>
  IR.Constraint (Either TMeta ty) ->
  m (IR.Constraint (Either TMeta ty))
solveMetas_Constraint = go id
  where
    go ::
      (MonadState s m, HasTypeMetas s s ty ty, HasKindMetas s) =>
      (ty -> a) ->
      IR.Constraint (Either TMeta a) ->
      m (IR.Constraint (Either TMeta a))
    go depth c =
      case c of
        IR.CSized t ->
          IR.CSized <$> solveTMetas_Type depth t
        IR.CForall n k rest ->
          IR.CForall n <$>
          solveKMetas k <*>
          (fmap sequence <$> go (F . depth) (sequence <$> rest))
        IR.CImplies a b ->
          IR.CImplies <$>
          go depth a <*>
          go depth b

solveTMetas_Expr ::
  (MonadState s m, HasTypeMetas s s ty ty) =>
  IR.Expr (Either TMeta ty) tm ->
  m (IR.Expr (Either TMeta ty) tm)
solveTMetas_Expr = go
  where
    go ::
      (MonadState s m, HasTypeMetas s s ty ty) =>
      IR.Expr (Either TMeta ty) tm ->
      m (IR.Expr (Either TMeta ty) tm)
    go e =
      case e of
        IR.Var a -> pure $ IR.Var a
        IR.Name n -> pure $ IR.Name n
        IR.Let bs rest ->
          IR.Let <$>
          (traverse.traverse) go bs <*>
          go rest
        IR.Inst n args ->
          IR.Inst n <$>
          traverse
            (solveTMetas_Type id)
            args
        IR.Call f args ->
          IR.Call <$>
          go f <*>
          traverse go args
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
        IR.New a -> IR.New <$> go a
        IR.Deref a -> IR.Deref <$> go a
