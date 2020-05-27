{-# language BangPatterns #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language ScopedTypeVariables #-}
module Check.Datatype where

import Bound (Scope, abstract, fromScope, toScope)
import Bound.Var (Var(..), unvar)
import Control.Applicative ((<|>))
import Control.Lens.Getter (use)
import Control.Monad ((<=<), guard, replicateM)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, evalStateT, runStateT)
import Data.Foldable (foldlM, traverse_)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Void (Void, absurd)

import Check.Entailment (HasGlobalTheory, HasSizeMetas, SMeta, Theory(..), freshSMeta, globalTheory)
import Check.Kind (checkKind, unifyKind)
import Check.TypeError (TypeError)
import IR (KMeta, Kind(..))
import qualified IR
import Size (Size(..))
import Syntax (Type)
import qualified Syntax
import TCState
  ( TMeta
  , TypeM, pattern TypeM, unTypeM
  , TCState, emptyTCState
  , HasKindMetas, HasTypeMetas
  , tmetaSolutions, kmetaSolutions
  , getTMeta, getKMeta, getTMetaKind
  , freshTMeta, freshKMeta
  , filterTypeSolutions
  , solveKMetas
  )

makeSizeTerm ::
  forall s m sz.
  ( MonadState s m, HasSizeMetas s, HasGlobalTheory s
  , MonadError TypeError m
  ) =>
  Vector SMeta ->
  Vector (Type (Var Int Void)) ->
  m (Size (Either SMeta sz))
makeSizeTerm sizeVars =
  foldlM (\acc a -> Plus acc <$> typeSizeTerm a) (Word 0)
  where
    typeSizeTerm :: Type (Var Int Void) -> m (Size (Either SMeta sz))
    typeSizeTerm t = do
      global <- use globalTheory
      let theory = Theory { _thGlobal = global, _thLocal = _ sizeVars }
      (assumes, subs) <- solve kindScope tyNames kinds theory (_ t)
      _

checkADT ::
  forall s m.
  ( MonadState s m
  , HasTypeMetas s s (Var Int Void) (Var Int Void)
  , HasKindMetas s
  , HasSizeMetas s
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
  sizeMetas <- Vector.replicateM (Vector.length paramNames) freshSMeta
  sz <-
    go
      (Map.insert datatypeName datatypeKind kScope)
      paramMetas
      sizeMetas
      0
      (Word 0)
      ctors
  ks <- traverse (solveKMetas . KVar) paramMetas
  let datatypeKind' = foldr KArr KType ks
  unifyKind datatypeKind' datatypeKind
  datatypeKind'' <- solveKMetas datatypeKind'
  pure (IR.substKMeta (const KType) datatypeKind'', _ sizeMetas sz)
  where
    go ::
      Map Text Kind ->
      Vector KMeta ->
      Vector SMeta ->
      Int ->
      Size (Either SMeta sz) ->
      Syntax.Ctors (Var Int Void) -> -- constructors
      m (Size (Either SMeta sz))
    go kindScope paramMetas sizeMetas !ctorCount sz c =
      case c of
        Syntax.End ->
          if ctorCount > 1
          then pure $ Plus (Word 8) sz
          else pure sz
        Syntax.Ctor ctorName ctorArgs ctorRest -> do
          traverse_
            (\ty ->
                checkKind
                  kindScope
                  (unvar (KVar . (paramMetas Vector.!)) absurd)
                  (TypeM $ Right <$> ty)
                  KType
            )
            ctorArgs
          sz' <- makeSizeTerm sizeMetas ctorArgs
          go
            kindScope
            paramMetas
            sizeMetas
            (ctorCount+1)
            (Max sz sz')
            ctorRest
