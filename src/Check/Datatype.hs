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
import IR (Constraint(..), KMeta, Kind(..), substKMeta)
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
  Vector SMeta ->
  Vector (Type (Var Int Void)) ->
  m (Size (Either SMeta Void))
makeSizeTerm kindScope paramNames paramKinds sizeVars =
  foldlM (\acc a -> plusSize acc <$> typeSizeTerm a) (Word 0)
  where
    typeSizeTerm :: Type (Var Int Void) -> m (Size (Either SMeta Void))
    typeSizeTerm t = do
      global <- use globalTheory
      local <-
        Vector.ifoldM
          (\acc ix s -> do
              k <- solveKMetas $ paramKinds Vector.! ix
              pure $
                Map.insert
                (Right . unvar (\() -> B ix) F <$> sizeConstraintFor 0 k)
                s
                acc
          )
          mempty
          sizeVars
      let
        theory :: Theory (Either TMeta (Var Int Void))
        theory =
          Theory
          { _thGlobal = global
          , _thLocal = local
          }
      placeholder <- freshSMeta
      (_assumes, subs) <-
        solve
          kindScope
          (unvar (paramNames Vector.!) absurd)
          (unvar (paramKinds Vector.!) absurd)
          theory
          [(placeholder, CSized $ fmap Right t)]
      pure $ findSMeta subs placeholder

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
  m (Kind, Size Void)
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
  sz <-
    adtSizeTerm
      kindScope
      paramKinds
      sizeMetas
      0
      (Word 0)
      ctors

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
      Vector SMeta ->
      Int ->
      Size (Either SMeta Void) ->
      Syntax.Ctors (Var Int Void) -> -- constructors
      m (Size (Either SMeta Void))
    adtSizeTerm kindScope paramKinds sizeMetas !ctorCount sz c =
      case c of
        Syntax.End ->
          if ctorCount > 1
          then pure $ plusSize (Word 8) sz
          else pure sz
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

          sz' <- makeSizeTerm kindScope paramNames paramKinds sizeMetas ctorArgs
          adtSizeTerm
            kindScope
            paramKinds
            sizeMetas
            (ctorCount+1)
            (maxSize sz sz')
            ctorRest
