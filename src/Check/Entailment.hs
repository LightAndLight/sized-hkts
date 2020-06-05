{-# language FlexibleContexts #-}
{-# language FlexibleInstances, MultiParamTypeClasses #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
{-# language TupleSections #-}
{-# language QuantifiedConstraints #-}
{-# options_ghc -fno-warn-unused-top-binds #-}
module Check.Entailment
  ( SMeta(..), composeSSubs
  , Theory(..), theoryToList, insertLocal, mapTy
  , HasGlobalTheory(..)
  , EntailState, emptyEntailState
  , entailTCState
  , entailSizeMeta
  , entailGlobalTheory
  , HasSizeMetas(..)
  , freshSMeta
  , findSMeta
  , solve
  , entails
  , simplify
  )
where

import Bound (abstract)
import Bound.Var (Var(..), unvar)
import Control.Applicative (empty)
import Control.Lens.Getter (use)
import Control.Lens.Lens (Lens')
import Control.Lens.Setter ((.=))
import Control.Lens.TH (makeLenses)
import Control.Monad (guard)
import Control.Monad.Except (MonadError, runExceptT, throwError)
import Control.Monad.State (MonadState, runStateT, get, put)
import Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import Data.Bifunctor (first)
import Data.Foldable (asum, foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Void (Void, absurd)

import Error.TypeError (TypeError(..), renderTyName)
import IR (Constraint(..), Kind)
import Size((.@), Size(..), pattern Var)
import Syntax (TMeta(..), TMeta, pattern TypeM)
import TCState
  ( TCState
  , HasDatatypeFields(..), HasConstraints(..)
  , FilterTypes, filterTypes, mapTypes
  , tcsGlobalTheory
  )
import Unify.Kind (HasKindMetas(..))
import Unify.TMeta (HasTypeMetas(..), freshTMeta, solveMetas_Constraint)
import Unify.Type (unifyType)

newtype SMeta = SMeta Int
  deriving (Eq, Ord, Show)

data Theory ty
  = Theory
  { _thGlobal :: Map (Constraint Void) (Size Void)
  , _thLocal :: Map (Constraint ty) SMeta
  }
makeLenses ''Theory

theoryToList :: Theory ty -> [(Size (Either SMeta sz), Constraint ty)]
theoryToList (Theory gbl lcl) =
  Map.foldrWithKey
    (\c m -> (:) (Var $ Left m, c))
    (Map.foldrWithKey (\c s -> (:) (absurd <$> s, absurd <$> c)) [] gbl)
    lcl

class HasGlobalTheory s where
  globalTheory :: Lens' s (Map (Constraint Void) (Size Void))

instance HasGlobalTheory (Theory ty) where
  globalTheory = thGlobal

instance HasGlobalTheory (TCState ty) where
  globalTheory = tcsGlobalTheory

insertLocal :: Ord ty => Constraint ty -> SMeta -> Theory ty -> Theory ty
insertLocal k v (Theory gbl lcl) = Theory gbl (Map.insert k v lcl)

mapTy :: Ord ty' => (ty -> ty') -> Theory ty -> Theory ty'
mapTy f (Theory gbl lcl) = Theory gbl (Map.mapKeys (fmap f) lcl)

applySSubs ::
  Map SMeta (Size (Either SMeta sz)) ->
  Size (Either SMeta sz) ->
  Size (Either SMeta sz)
applySSubs subs s =
  s >>= either (\m -> fromMaybe (Var $ Left m) $ Map.lookup m subs) (Var . Right)

findSMeta ::
  Map SMeta (Size (Either SMeta sz)) ->
  SMeta ->
  Size (Either SMeta sz)
findSMeta s m =
  case Map.lookup m s of
    Nothing -> Var $ Left m
    Just term -> term >>= either (findSMeta s) (Var . Right)

composeSSubs ::
  Map SMeta (Size (Either SMeta sz)) ->
  Map SMeta (Size (Either SMeta sz)) ->
  Map SMeta (Size (Either SMeta sz))
composeSSubs a b =
  fmap (applySSubs a) b <> a

data EntailState tc ty
  = EntailState
  { _entailTCState :: tc ty
  , _entailSizeMeta :: SMeta
  , _entailGlobalTheory :: Map (Constraint Void) (Size Void)
  }
makeLenses ''EntailState

instance HasGlobalTheory (tc ty) => HasGlobalTheory (EntailState tc ty) where
  globalTheory = entailGlobalTheory

instance HasConstraints tc => HasConstraints (EntailState tc) where
  requiredConstraints = entailTCState.requiredConstraints

instance FilterTypes tc => FilterTypes (EntailState tc) where
  filterTypes f es = es { _entailTCState = filterTypes f $ _entailTCState es }

class HasSizeMetas s where
  nextSMeta :: Lens' s SMeta

instance HasTypeMetas tc => HasTypeMetas (EntailState tc) where
  nextTMeta = entailTCState.nextTMeta
  tmetaKinds = entailTCState.tmetaKinds
  tmetaSolutions = entailTCState.tmetaSolutions

instance HasKindMetas (tc ty) => HasKindMetas (EntailState tc ty) where
  nextKMeta = entailTCState.nextKMeta
  kmetaSolutions = entailTCState.kmetaSolutions

instance HasSizeMetas (EntailState tc ty) where
  nextSMeta = entailSizeMeta

instance HasDatatypeFields (tc ty) => HasDatatypeFields (EntailState tc ty) where
  datatypeFields = entailTCState.datatypeFields

emptyEntailState :: tc ty -> EntailState tc ty
emptyEntailState tc =
  EntailState
  { _entailTCState = tc
  , _entailSizeMeta = SMeta 0
  , _entailGlobalTheory = mempty
  }

freshSMeta :: (MonadState s m, HasSizeMetas s) => m SMeta
freshSMeta = do
  SMeta t <- use nextSMeta
  nextSMeta .= SMeta (t+1)
  pure $ SMeta t

withoutMetas :: (ty -> ty') -> Constraint (Either TMeta ty) -> Maybe (Constraint ty')
withoutMetas f = traverse (either (const Nothing) (Just . f))

solve ::
  ( MonadState (s ty) m
  , FilterTypes s, HasTypeMetas s
  , forall x. HasKindMetas (s x), forall x. HasSizeMetas (s x)
  , MonadError TypeError m
  , Ord ty
  ) =>
  Map Text Kind ->
  (ty -> Either Int Text) ->
  (ty -> Kind) ->
  Theory (Either TMeta ty) ->
  [(SMeta, Constraint (Either TMeta ty))] ->
  m
    ( [(SMeta, Constraint (Either TMeta ty))]
    , Map SMeta (Size (Either SMeta Void))
    )
solve _ _ _ _ [] = pure ([], mempty)
solve kindScope tyNames kinds theory (c:cs) = do
  m_res <- runMaybeT $ simplify kindScope tyNames kinds theory c
  case m_res of
    Nothing -> do
      c' <- solveMetas_Constraint (snd c)
      case withoutMetas (Right . renderTyName . tyNames) c' of
        Nothing -> do
          (cs', sols') <- solve kindScope tyNames kinds theory cs
          pure ((fst c, c') : cs', sols')
        Just c'' -> throwError $ CouldNotDeduce c''
    Just (cs', sols) -> do
      (cs'', sols') <- solve kindScope tyNames kinds theory (cs' <> cs)
      pure (cs'', composeSSubs sols' sols)

entails ::
  ( MonadState (s ty) m, HasKindMetas (s ty), HasTypeMetas s, HasSizeMetas (s ty)
  , Eq ty
  ) =>
  Map Text Kind ->
  (ty -> Either Int Text) ->
  (ty -> Kind) ->
  (Size (Either SMeta sz), Constraint (Either TMeta ty)) ->
  (SMeta, Constraint (Either TMeta ty)) ->
  MaybeT m
    ( [(SMeta, Constraint (Either TMeta ty))]
    , Map SMeta (Size (Either SMeta sz))
    )
entails kindScope tyNames kinds (antSize, ant) (consVar, cons) =
  case ant of
    -- antSize : forall (x : k). _
    CForall _ k a -> do
      meta <- freshTMeta k
      entails kindScope tyNames kinds (antSize, unvar (\() -> Left meta) id <$> a) (consVar, cons)
    -- antSize : _ -> _
    CImplies a b -> do
      bvar <- freshSMeta
      (bAssumes, ssubs) <- entails kindScope tyNames kinds (Var $ Left bvar, b) (consVar, cons)
      avar <- freshSMeta
      pure
        ( (avar, a) : bAssumes
        , composeSSubs (Map.singleton bvar $ antSize .@ Var (Left avar)) ssubs
        )
    -- antSize : Word64
    CSized t ->
      case cons of
        CSized t' -> do
          res <- runExceptT $ unifyType kindScope tyNames kinds (TypeM t') (TypeM t)
          case res of
            Left{} -> empty
            Right () -> pure ([], Map.singleton consVar antSize)
        _ -> error "consequent not simple enough"

simplify ::
  ( MonadState (s ty) m
  , FilterTypes s, HasTypeMetas s
  , forall x. HasKindMetas (s x), forall x. HasSizeMetas (s x)
  , MonadError TypeError m
  , Ord ty
  ) =>
  Map Text Kind ->
  (ty -> Either Int Text) ->
  (ty -> Kind) ->
  Theory (Either TMeta ty) ->
  (SMeta, Constraint (Either TMeta ty)) ->
  m
    ( [(SMeta, Constraint (Either TMeta ty))]
    , Map SMeta (Size (Either SMeta sz))
    )
simplify kindScope tyNames kinds theory (consVar, cons) =
  case cons of
    CForall m_n k a -> do
      ameta <- freshSMeta
      es <- get
      ((aAssumes, asubs), es') <-
        flip runStateT (mapTypes F es) $
        simplify
          kindScope
          (unvar (\() -> maybe (Left 0) Right m_n) (first (+1) . tyNames))
          (unvar (\() -> k) kinds)
          (mapTy (fmap F) theory)
          (ameta, sequence <$> a)
      put $ filterTypes (unvar (\() -> Nothing) Just) es'
      pure
        ( (fmap.fmap) (CForall m_n k . fmap sequence) aAssumes
        , Map.singleton consVar (fromMaybe (error "ameta not solved") $ Map.lookup ameta asubs)
        )
    CImplies a b -> do
      ameta <- freshSMeta
      bmeta <- freshSMeta
      (bAssumes, bsubs) <- simplify kindScope tyNames kinds (insertLocal a ameta theory) (bmeta, b)
      bAssumes' <- traverse (\assume -> (, assume) <$> freshSMeta) bAssumes
      pure
        ( (\(v, (_, c)) -> (v, c)) <$> bAssumes'
        , Map.singleton consVar $
          Lam
            (abstract (either (guard . (ameta ==)) (const Nothing)) $
             applySSubs
               (foldl'
                  (\acc (new, (old, _)) ->
                     Map.insert old ((Var $ Left new) .@ (Var $ Left ameta)) acc
                  )
                  mempty
                  bAssumes'
               )
               (fromMaybe (error "bmeta not solved") $ Map.lookup bmeta bsubs)
            )
        )
    CSized{} -> do
      m_res <-
        runMaybeT . asum $
          (\(antVar, ant) -> entails kindScope tyNames kinds (antVar, ant) (consVar, cons)) <$>
          theoryToList theory
      case m_res of
        Nothing -> do
          cons' <- solveMetas_Constraint cons
          throwError $ CouldNotDeduce ((fmap.fmap) (renderTyName . tyNames) cons')
        Just (assumes, sub) -> pure (assumes, sub)
