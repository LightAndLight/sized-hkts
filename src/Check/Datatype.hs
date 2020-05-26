{-# language BangPatterns #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language ScopedTypeVariables #-}
module Check.Datatype where

import Bound (Scope, fromScope, toScope)
import Bound.Var (Var(..), unvar)
import Control.Applicative ((<|>))
import Control.Monad (replicateM)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, evalStateT, runStateT)
import Data.Foldable (traverse_)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Void (Void, absurd)

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
  forall sz.
  (Int -> Maybe sz) ->
  Vector (Type (Var Int Void)) ->
  Size sz
makeSizeTerm sizeVars =
  foldl (\acc a -> Plus acc (typeSizeTerm a)) (Word 0)
  where
    typeSizeTerm :: Type (Var Int Void) -> Size sz
    typeSizeTerm t = _

checkADT ::
  forall s m.
  ( MonadState s m
  , HasTypeMetas s s (Var Int Void) (Var Int Void)
  , HasKindMetas s
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
  sz <-
    abstractParams
      (Map.insert datatypeName datatypeKind kScope)
      paramMetas
      (const Nothing)
      id
      ctors
      (Vector.toList paramNames)
  ks <- traverse (solveKMetas . KVar) paramMetas
  let datatypeKind' = foldr KArr KType ks
  unifyKind datatypeKind' datatypeKind
  datatypeKind'' <- solveKMetas datatypeKind'
  pure (IR.substKMeta (const KType) datatypeKind'', sz)
  where
    abstractParams ::
      Map Text Kind ->
      Vector KMeta ->
      (Int -> Maybe sz) ->
      (Size sz -> Size Void) ->
      Syntax.Ctors (Var Int Void) -> -- constructors
      [Text] ->
      m (Size Void)
    abstractParams kindScope paramMetas sizeVars mkSize c params =
      case params of
        [] ->
          go
            kindScope
            paramMetas
            0
            sizeVars
            mkSize
            (Word 0)
            c
        p:ps ->
          abstractParams
            kindScope
            paramMetas
            (\ix -> F <$> sizeVars ix <|> Just (B ()))
            (mkSize . Lam . toScope)
            c
            ps

    go ::
      Map Text Kind ->
      Vector KMeta ->
      Int ->
      (Int -> Maybe sz) ->
      (Size sz -> Size Void) ->
      Size sz ->
      Syntax.Ctors (Var Int Void) -> -- constructors
      m (Size Void)
    go kindScope paramMetas !ctorCount sizeVars mkSize sz c =
      case c of
        Syntax.End ->
          if ctorCount > 1
          then pure $ Plus (Word 8) (mkSize sz)
          else pure $ mkSize sz
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
          go
            kindScope
            paramMetas
            (ctorCount+1)
            sizeVars
            mkSize
            (Max sz (makeSizeTerm sizeVars ctorArgs))
            ctorRest
