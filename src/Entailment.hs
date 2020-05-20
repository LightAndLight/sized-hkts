{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
{-# language TupleSections #-}
module Entailment where

import Bound ((>>>=), Scope, abstract, instantiate1)
import Bound.Var (Var(..), unvar)
import Control.Applicative (empty)
import Control.Monad (ap, guard)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, gets, modify)
import Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Foldable (asum, foldl')
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Void (Void, absurd)
import Data.Word (Word64)

import IR (Constraint(..), Kind)
import Typecheck (TMeta(..), TypeM, pattern TypeM, unifyType, applyTSubs_Constraint)

data Size a
  = Lam (Scope () Size a)
  | App a [Size a]
  | Plus (Size a) (Size a)
  | Word Word64
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Size
deriveShow1 ''Size
instance Eq a => Eq (Size a) where; (==) = eq1
instance Show a => Show (Size a) where; showsPrec = showsPrec1
instance Applicative Size where; pure a = App a []; (<*>) = ap
instance Monad Size where -- probably not lawful, but it's helpful to have everything be 'beta-normal'
  Lam a >>= f = Lam (a >>>= f)
  App a bs >>= f = foldl (.@) (f a) ((>>= f) <$> bs)
  Plus a b >>= f =
    let
      a' = a >>= f
      b' = b >>= f
    in
      case (a', b') of
        (Word m, Word n) -> Word (m + n)
        _ -> Plus a' b'
  Word n >>= _ = Word n

pattern Var :: a -> Size a
pattern Var a = App a []

infixl 5 .@
(.@) :: Size a -> Size a -> Size a
(.@) (Lam f) x = instantiate1 x f
(.@) (App a bs) x = App a (bs ++ [x])
(.@) Word{} _ = error "applying to Word"
(.@) Plus{} _ = error "applying to Plus"

data Theory ty
  = Theory
  { thGlobal :: Map (Constraint Void) (Size Void)
  , thLocal :: Map (Constraint ty) SMeta
  }

theoryToList :: Theory ty -> [(Size (Either SMeta sz), Constraint ty)]
theoryToList (Theory gbl lcl) =
  Map.foldrWithKey
    (\c m -> (:) (Var $ Left m, c))
    (Map.foldrWithKey (\c s -> (:) (absurd <$> s, absurd <$> c)) [] gbl)
    lcl

insertLocal :: Ord ty => Constraint ty -> SMeta -> Theory ty -> Theory ty
insertLocal k v (Theory gbl lcl) = Theory gbl (Map.insert k v lcl)

mapTy :: Ord ty' => (ty -> ty') -> Theory ty -> Theory ty'
mapTy f (Theory gbl lcl) = Theory gbl (Map.mapKeys (fmap f) lcl)

newtype SMeta = SMeta Int
  deriving (Eq, Ord, Show)

applySSubs ::
  Map SMeta (Size (Either SMeta sz)) ->
  Size (Either SMeta sz) ->
  Size (Either SMeta sz)
applySSubs subs s =
  s >>= either (\m -> fromMaybe (Var $ Left m) $ Map.lookup m subs) (Var . Right)

composeSSubs ::
  Map SMeta (Size (Either SMeta sz)) ->
  Map SMeta (Size (Either SMeta sz)) ->
  Map SMeta (Size (Either SMeta sz))
composeSSubs a b =
  fmap (applySSubs a) b <> a

data EntailState
  = EntailState
  { entailTypeMeta :: TMeta
  , entailTypeMetaKinds :: Map TMeta Kind
  , entailSizeMeta :: SMeta
  }

emptyEntailState :: EntailState
emptyEntailState =
  EntailState
  { entailTypeMeta = TMeta 0
  , entailTypeMetaKinds = mempty
  , entailSizeMeta = SMeta 0
  }

freshTMeta :: MonadState EntailState m => Kind -> m TMeta
freshTMeta k = do
  TMeta t <- gets entailTypeMeta
  modify $
    \s -> s { entailTypeMeta = TMeta (t+1), entailTypeMetaKinds = Map.insert (TMeta t) k (entailTypeMetaKinds s) }
  pure $ TMeta t

freshSMeta :: MonadState EntailState m => m SMeta
freshSMeta = do
  SMeta t <- gets entailSizeMeta
  modify $
    \s -> s { entailSizeMeta = SMeta (t+1) }
  pure $ SMeta t

withoutMetas :: (ty -> ty') -> Constraint (Either TMeta ty) -> Maybe (Constraint ty')
withoutMetas f = traverse (either (const Nothing) (Just . f))

data EntailError
  = CouldNotDeduce (Constraint (Either TMeta Text))
  deriving (Eq, Show)

solve ::
  (MonadState EntailState m, MonadError EntailError m, Ord ty) =>
  (ty -> Text) ->
  (ty -> Kind) ->
  Theory (Either TMeta ty) ->
  [(SMeta, Constraint (Either TMeta ty))] ->
  m
    ( [(SMeta, Constraint (Either TMeta ty))]
    , Map SMeta (Size (Either SMeta sz))
    )
solve _ _ _ [] = pure ([], mempty)
solve tyNames kinds theory (c:cs) = do
  m_res <- runMaybeT $ simplify tyNames kinds theory c
  case m_res of
    Nothing -> do
      case withoutMetas (Right . tyNames) (snd c) of
        Nothing -> do
          (cs', sols') <- solve tyNames kinds theory cs
          pure (c : cs', sols')
        Just c' -> throwError $ CouldNotDeduce c'
    Just (cs', sols) -> do
      (cs'', sols') <- solve tyNames kinds theory (cs' <> cs)
      pure (cs'', composeSSubs sols' sols)

entails ::
  (MonadState EntailState m, Eq ty) =>
  (ty -> Text) ->
  (ty -> Kind) ->
  (Size (Either SMeta sz), Constraint (Either TMeta ty)) ->
  (SMeta, Constraint (Either TMeta ty)) ->
  MaybeT m
    ( [(SMeta, Constraint (Either TMeta ty))]
    , Map TMeta (TypeM ty)
    , Map SMeta (Size (Either SMeta sz))
    )
entails tyNames kinds (antSize, ant) (consVar, cons) =
  case ant of
    -- antSize : forall (x : k). _
    CForall _ k a -> do
      meta <- freshTMeta k
      entails tyNames kinds (antSize, unvar (\() -> Left meta) id <$> a) (consVar, cons)
    -- antSize : _ -> _
    CImplies a b -> do
      bvar <- freshSMeta
      (bAssumes, tsubs, ssubs) <- entails tyNames kinds (Var $ Left bvar, b) (consVar, cons)
      avar <- freshSMeta
      pure
        ( (avar, applyTSubs_Constraint tsubs a) : bAssumes
        , tsubs
        , composeSSubs (Map.singleton bvar $ antSize .@ Var (Left avar)) ssubs
        )
    -- antSize : Word64
    CSized t ->
      case cons of
        CSized t' ->
          case unifyType tyNames kinds (TypeM t') (TypeM t) of
            Left{} -> empty
            Right sub -> pure ([], sub, Map.singleton consVar antSize)
        _ -> error "consequent not simple enough"

simplify ::
  (MonadState EntailState m, MonadError EntailError m, Ord ty) =>
  (ty -> Text) ->
  (ty -> Kind) ->
  Theory (Either TMeta ty) ->
  (SMeta, Constraint (Either TMeta ty)) ->
  m
    ( [(SMeta, Constraint (Either TMeta ty))]
    , Map SMeta (Size (Either SMeta sz))
    )
simplify tyNames kinds theory (consVar, cons) =
  case cons of
    CForall n k a -> do
      ameta <- freshSMeta
      (aAssumes, asubs) <-
        simplify
          (unvar (\() -> n) tyNames)
          (unvar (\() -> k) kinds)
          (mapTy (fmap F) theory)
          (ameta, sequence <$> a)
      pure
        ( (fmap.fmap) (CForall n k . fmap sequence) aAssumes
        , Map.singleton consVar (fromMaybe (error "ameta not solved") $ Map.lookup ameta asubs)
        )
    CImplies a b -> do
      ameta <- freshSMeta
      bmeta <- freshSMeta
      (bAssumes, bsubs) <- simplify tyNames kinds (insertLocal a ameta theory) (bmeta, b)
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
          (\(antVar, ant) -> entails tyNames kinds (antVar, ant) (consVar, cons)) <$>
          theoryToList theory
      case m_res of
        Nothing -> throwError $ CouldNotDeduce ((fmap.fmap) tyNames cons)
        Just (assumes, _, sub) -> pure (assumes, sub)
