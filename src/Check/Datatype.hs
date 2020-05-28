{-# language BangPatterns #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language ScopedTypeVariables #-}
{-# language QuantifiedConstraints #-}
module Check.Datatype where

import Bound (abstract)
import Bound.Var (Var(..), unvar)
import Control.Lens.Getter (use)
import Control.Monad (guard)
import Control.Monad.Except (MonadError)
import Control.Monad.State (MonadState)
import Data.Foldable (foldlM, traverse_)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Void (Void, absurd)

import Check.Entailment
  ( HasGlobalTheory, HasSizeMetas
  , SMeta, Theory(..)
  , freshSMeta, findSMeta
  , globalTheory
  , solve
  )
import Check.Kind (checkKind, unifyKind)
import Check.TypeError (TypeError)
import IR (Constraint(..), KMeta, Kind(..), bindConstraint, substKMeta)
import Size (Size(..), plusSize, maxSize, sizeConstraintFor)
import Syntax (Type(..))
import qualified Syntax
import TCState
  ( TMeta, pattern TypeM
  , HasKindMetas, HasTypeMetas
  , freshKMeta
  , solveKMetas
  )

makeSizeTerm ::
  forall s m.
  ( MonadState (s (Var Int Void)) m
  , HasTypeMetas s
  , forall x. HasKindMetas (s x)
  , forall x. HasSizeMetas (s x)
  , forall x. HasGlobalTheory (s x)
  , MonadError TypeError m
  ) =>
  Map Text Kind ->
  Vector Text ->
  Vector Kind ->
  Map (Constraint (Either TMeta (Var Int Void))) SMeta ->
  Vector (Type (Var Int Void)) ->
  m (Set SMeta, Size (Either SMeta Void))
makeSizeTerm kindScope paramNames paramKinds assumedConstraints argTypes = do
  global <- use globalTheory
  let
    theory :: Theory (Either TMeta (Var Int Void))
    theory =
      Theory
      { _thGlobal = global
      , _thLocal = assumedConstraints
      }
  foldlM
    (\(usedSizeMetas, sz) a -> do
        sz' <- typeSizeTerm theory a
        pure (usedSizeMetas <> foldMap (either Set.singleton absurd) sz', plusSize sz sz')
    )
    (mempty, Word 0)
    argTypes
  where
    typeSizeTerm :: Theory (Either TMeta (Var Int Void)) -> Type (Var Int Void) -> m (Size (Either SMeta Void))
    typeSizeTerm theory t = do
      placeholder <- freshSMeta
      (_assumes, subs) <-
        solve
          kindScope
          (unvar (paramNames Vector.!) absurd)
          (unvar (paramKinds Vector.!) absurd)
          theory
          [(placeholder, CSized $ Right <$> t)]
      pure $ findSMeta subs placeholder

-- | Given some assumptions and an instance head, construct an axiom type
makeSizeConstraint ::
  Vector (Constraint (Either TMeta (Var Int Void))) ->
  Type (Either TMeta (Var Int Void)) ->
  Constraint Void
makeSizeConstraint as = _ $ go 0 (Vector.toList as)
  where
    go ::
      Int -> -- the remaining entries
      [Constraint (Either TMeta (Var Int Void))] ->
      Type (Either TMeta (Var Int Void)) ->
      Constraint (Either TMeta (Var Int Void))
    go !n assumes hd =
      case assumes of
        [] -> CSized hd
        a:rest ->
          let
            hd' = go (n+1) rest hd
          in
            CForall (error "TODO") (error "TODO") . CImplies (F <$> a) $
            bindConstraint
              (either
                 (TVar . F . Left)
                 (unvar (\ix -> if ix == n then TVar $ B () else TVar $ F $ Right $ B ix) absurd)
              )
              hd'

checkADT ::
  forall s m.
  ( MonadState (s (Var Int Void)) m
  , HasTypeMetas s
  , forall x. HasKindMetas (s x)
  , forall x. HasSizeMetas (s x)
  , forall x. HasGlobalTheory (s x)
  , MonadError TypeError m
  ) =>
  Map Text Kind ->
  Text -> -- name
  Vector Text -> -- type parameters
  Syntax.Ctors (Var Int Void) -> -- constructors
  m (Kind, Constraint Void, Size Void)
checkADT kScope datatypeName paramNames ctors = do
  datatypeKind <- KVar <$> freshKMeta
  paramMetas <- Vector.replicateM (Vector.length paramNames) freshKMeta

  let kindScope = Map.insert datatypeName datatypeKind kScope
  adtKinds kindScope paramMetas ctors

  ks <- traverse (solveKMetas . KVar) paramMetas
  let datatypeKind' = foldr KArr KType ks
  unifyKind datatypeKind' datatypeKind
  datatypeKind'' <-
    substKMeta (const KType) <$>
    solveKMetas datatypeKind'

  sizeMetas <- Vector.replicateM (Vector.length paramNames) freshSMeta
  paramKinds <- traverse (fmap (substKMeta $ const KType) . solveKMetas . KVar) paramMetas
  let
    assumedConstraintsFwd :: Map (Constraint (Either TMeta (Var Int Void))) SMeta
    assumedConstraintsBwd :: Map SMeta (Constraint (Either TMeta (Var Int Void)))
    (assumedConstraintsFwd, assumedConstraintsBwd) =
      Vector.ifoldl'
        (\(accFwd, accBwd) ix s ->
           let
             k = paramKinds Vector.! ix
             c = Right . unvar (\() -> B ix) F <$> sizeConstraintFor 0 k
           in
             ( Map.insert c s accFwd
             , Map.insert s c accBwd
             )
        )
        (mempty, mempty)
        sizeMetas

  (usedSizeMetas, sz) <-
    adtSizeTerm
      kindScope
      paramKinds
      assumedConstraintsFwd
      0
      mempty
      (Word 0)
      ctors

  let
    usedConstraints :: Vector (Constraint (Either TMeta (Var Int Void)))
    usedConstraints =
      Vector.map (assumedConstraintsBwd Map.!) $
      Vector.filter (`Set.member` usedSizeMetas) sizeMetas

    axiomHead :: Type (Either TMeta (Var Int Void))
    axiomHead =
      foldl
        (\acc ix -> TApp acc (TVar $ Right $ B ix))
        (TName datatypeName)
        [0..length paramNames - 1]

  let
    m_sz' =
      traverse
        (either (const Nothing) Just)
        (foldr
           (\s -> Lam . abstract (either (guard . (s ==)) (const Nothing)))
           sz
           sizeMetas
        )
  case m_sz' of
    Nothing -> error "failed to abstract over all SMetas"
    Just sz' ->
      pure
        ( IR.substKMeta (const KType) datatypeKind''
        , makeSizeConstraint usedConstraints axiomHead
        , sz'
        )
  where
    adtKinds ::
      Map Text Kind ->
      Vector KMeta ->
      Syntax.Ctors (Var Int Void) -> -- constructors
      m ()
    adtKinds kindScope paramMetas c =
      case c of
        Syntax.End -> pure ()
        Syntax.Ctor _ctorName ctorArgs ctorRest -> do
          let paramKinds = KVar <$> paramMetas
          traverse_
            (\ty ->
                checkKind
                  kindScope
                  (unvar (paramKinds Vector.!) absurd)
                  (TypeM $ Right <$> ty)
                  KType
            )
            ctorArgs
          adtKinds kindScope paramMetas ctorRest

    adtSizeTerm ::
      Map Text Kind ->
      Vector Kind ->
      Map (Constraint (Either TMeta (Var Int Void))) SMeta ->
      Int ->
      Set SMeta ->
      Size (Either SMeta Void) ->
      Syntax.Ctors (Var Int Void) -> -- constructors
      m (Set SMeta, Size (Either SMeta Void))
    adtSizeTerm kindScope paramKinds assumedConstraints !ctorCount !usedConstraints sz c =
      case c of
        Syntax.End ->
          pure $!
          if ctorCount > 1
          then (usedConstraints, plusSize (Word 8) sz)
          else (usedConstraints, sz)
        Syntax.Ctor _ctorName ctorArgs ctorRest -> do
          traverse_
            (\ty ->
                checkKind
                  kindScope
                  (unvar (paramKinds Vector.!) absurd)
                  (TypeM $ Right <$> ty)
                  KType
            )
            ctorArgs

          (usedConstraints', sz') <- makeSizeTerm kindScope paramNames paramKinds assumedConstraints ctorArgs
          adtSizeTerm
            kindScope
            paramKinds
            assumedConstraints
            (ctorCount+1)
            (usedConstraints <> usedConstraints')
            (maxSize sz sz')
            ctorRest
