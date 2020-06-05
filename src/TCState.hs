{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language FunctionalDependencies, MultiParamTypeClasses, TypeFamilies #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
module TCState
  ( TCState
  , emptyTCState
  , tcsKindMeta
  , tcsKindSolutions
  , tcsTypeMeta
  , tcsTypeMetaKinds
  , tcsTypeSolutions
  , tcsConstraints
  , tcsGlobalTheory
  , HasTypeMetas(..), HasKindMetas(..), HasConstraints(..)
  , FilterTypes(..), mapTypes
  , freshTMeta, freshKMeta
  , getTMeta, getKMeta
  , getTMetaKind
  , solveKMetas, solveKMetasMaybe
  , solveTMetas_Type
  , solveTMetas_Expr
  , solveMetas_Constraint
  , HasDatatypeFields(..)
  , getFieldType
  )
where

import Bound.Var (Var(..))
import Control.Applicative (empty)
import Control.Lens.Getter ((^.), use, uses)
import Control.Lens.Lens (Lens')
import Control.Lens.Setter ((%=), (.=))
import Control.Lens.TH (makeLenses)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import Data.Bitraversable (bitraverse)
import Data.Foldable (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Vector as Vector
import Data.Void (Void)

import Error.TypeError (TypeError(..))
import IR (Constraint, KMeta(..), Kind(..))
import qualified IR
import Size (Size)
import Syntax (TMeta(..), Type(..), TypeM, unTypeM)

data TCState ty
  = TCState
  { _tcsKindMeta :: KMeta
  , _tcsKindSolutions :: Map KMeta Kind
  , _tcsTypeMeta :: TMeta
  , _tcsTypeMetaKinds :: Map TMeta Kind
  , _tcsTypeSolutions :: Map TMeta (TypeM ty)
  , _tcsConstraints :: Set (Constraint (Either TMeta ty))
  , _tcsGlobalTheory :: Map (Constraint Void) (Size Void)
  , _tcsDatatypeFields :: Map Text IR.Fields
  }
makeLenses ''TCState

emptyTCState :: Ord ty => TCState ty
emptyTCState =
  TCState
  { _tcsKindMeta = KMeta 0
  , _tcsKindSolutions = mempty
  , _tcsTypeMeta = TMeta 0
  , _tcsTypeMetaKinds = mempty
  , _tcsTypeSolutions = mempty
  , _tcsConstraints = mempty
  , _tcsGlobalTheory = mempty
  , _tcsDatatypeFields = mempty
  }

class FilterTypes s where
  filterTypes :: Ord ty' => (ty -> Maybe ty') -> s ty -> s ty'

mapTypes :: (FilterTypes s, Ord ty') => (ty -> ty') -> s ty -> s ty'
mapTypes f = filterTypes (Just . f)

class HasConstraints s where
  requiredConstraints :: Lens' (s ty) (Set (Constraint (Either TMeta ty)))

instance HasConstraints TCState where
  requiredConstraints = tcsConstraints

class HasTypeMetas s where
  nextTMeta :: Lens' (s ty) TMeta
  tmetaKinds :: Lens' (s ty) (Map TMeta Kind)
  tmetaSolutions :: Lens' (s ty) (Map TMeta (TypeM ty))

instance HasTypeMetas TCState where
  nextTMeta = tcsTypeMeta
  tmetaKinds = tcsTypeMetaKinds
  tmetaSolutions = tcsTypeSolutions

class HasKindMetas s where
  nextKMeta :: Lens' s KMeta
  kmetaSolutions :: Lens' s (Map KMeta Kind)

instance HasKindMetas (TCState ty) where
  nextKMeta = tcsKindMeta
  kmetaSolutions = tcsKindSolutions

instance FilterTypes TCState where
  filterTypes f tcs =
    let
      (tmetas, sols') =
        Map.foldrWithKey
          (\k a (ms, ss) ->
            case traverse f a of
              Nothing -> (k:ms, ss)
              Just a' -> (ms, Map.insert k a' ss)
          )
          ([], mempty)
          (tcs ^. tcsTypeSolutions)
      kinds' = foldl' (flip Map.delete) (tcs ^. tcsTypeMetaKinds) tmetas
      constraints' =
        foldr
          (\c ->
             case traverse (either (Just . Left) (fmap Right . f)) c of
               Nothing -> id
               Just c' -> Set.insert c'
          )
          mempty
          (tcs ^. tcsConstraints)
    in
      tcs
      { _tcsTypeMetaKinds = kinds'
      , _tcsTypeSolutions = sols'
      , _tcsConstraints = constraints'
      }

freshKMeta :: (MonadState s m, HasKindMetas s) => m KMeta
freshKMeta = do
  KMeta k <- use nextKMeta
  nextKMeta .= KMeta (k+1)
  pure $ KMeta k

freshTMeta :: (MonadState (s ty) m, HasTypeMetas s) => Kind -> m TMeta
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
  (MonadState (s ty) m, HasTypeMetas s) =>
  TMeta ->
  m (Maybe (TypeM ty))
getTMeta v = do
  sols <- use tmetaSolutions
  pure $ Map.lookup v sols

getTMetaKind :: (MonadState (s ty) m, HasTypeMetas s) => TMeta -> m (Maybe Kind)
getTMetaKind v = do
  ks <- use tmetaKinds
  pure $ Map.lookup v ks

solveTMetas_Type ::
  (MonadState (s ty) m, HasTypeMetas s) =>
  (ty -> a) ->
  Type (Either TMeta a) ->
  m (Type (Either TMeta a))
solveTMetas_Type d = go d
  where
    go ::
      (MonadState (s ty) m, HasTypeMetas s) =>
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
        TInt32 -> pure TInt32
        TBool -> pure TBool
        TPtr -> pure TPtr
        TFun ts -> TFun <$> traverse (go depth) ts
        TName n -> pure $ TName n

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

solveMetas_Constraint ::
  (MonadState (s ty) m, HasTypeMetas s, HasKindMetas (s ty)) =>
  IR.Constraint (Either TMeta ty) ->
  m (IR.Constraint (Either TMeta ty))
solveMetas_Constraint = go id
  where
    go ::
      (MonadState (s ty) m, HasTypeMetas s, HasKindMetas (s ty)) =>
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
  (MonadState (s ty) m, HasTypeMetas s) =>
  IR.Expr (Either TMeta ty) tm ->
  m (IR.Expr (Either TMeta ty) tm)
solveTMetas_Expr = go
  where
    goCase ::
      (MonadState (s ty) m, HasTypeMetas s) =>
      IR.Case (Either TMeta ty) tm ->
      m (IR.Case (Either TMeta ty) tm)
    goCase (IR.Case name args e) =
      IR.Case name args <$> go e

    go ::
      (MonadState (s ty) m, HasTypeMetas s) =>
      IR.Expr (Either TMeta ty) tm ->
      m (IR.Expr (Either TMeta ty) tm)
    go e =
      case e of
        IR.Var a -> pure $ IR.Var a
        IR.Name n -> pure $ IR.Name n
        IR.Let bs rest ->
          IR.Let <$>
          traverse (bitraverse (traverse go) (solveTMetas_Type id)) bs <*>
          go rest
        IR.Inst n args ->
          IR.Inst n <$>
          traverse
            (solveTMetas_Type id)
            args
        IR.Ctor n ts ->
          IR.Ctor n <$>
          traverse
            (solveTMetas_Type id)
            ts
        IR.Call f args t ->
          IR.Call <$>
          go f <*>
          traverse go args <*>
          solveTMetas_Type id t
        IR.Int32 n -> pure $ IR.Int32 n
        IR.BTrue -> pure $ IR.BTrue
        IR.BFalse -> pure $ IR.BFalse
        IR.New a t -> IR.New <$> go a <*> solveTMetas_Type id t
        IR.Deref a -> IR.Deref <$> go a
        IR.Project a b -> (\a' -> IR.Project a' b) <$> go a
        IR.Match a b -> IR.Match <$> go a <*> traverse goCase b

class HasDatatypeFields s where
  datatypeFields :: Lens' s (Map Text IR.Fields)

instance HasDatatypeFields (TCState ty) where
  datatypeFields = tcsDatatypeFields

getFieldType ::
  ( MonadState s m, HasDatatypeFields s
  , MonadError TypeError m
  ) =>
  Text ->
  IR.Projection ->
  m (Maybe (Type (Var Int Void)))
getFieldType tyName prj = do
  m_fs <- uses datatypeFields $ Map.lookup tyName
  case m_fs of
    Nothing -> throwError $ TNotInScope tyName
    Just fs ->
      pure $ case prj of
        IR.Numeric ix ->
          case fs of
            IR.Unnamed fs' -> Just $ fs' Vector.! fromIntegral ix
            _ -> Nothing
        IR.Field n ->
          case fs of
            IR.Named fs' -> Map.lookup n fs'
            _ -> Nothing
