{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language QuantifiedConstraints #-}
{-# language ScopedTypeVariables #-}
module Compile where

import Bound.Var (Var)
import Control.Lens.Setter ((%=))
import Control.Monad.Except (MonadError)
import Control.Monad.State (MonadState, evalStateT)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import Data.Void (Void)

import Check.Datatype (checkADT)
import Check.Entailment (HasSizeMetas, HasGlobalTheory, emptyEntailState, globalTheory)
import Check.Function (checkFunction)
import Check.TypeError (TypeError)
import qualified Codegen
import qualified Codegen.C as C
import qualified IR
import TCState (FilterTypes, HasTypeMetas, HasKindMetas, emptyTCState)
import Size (Size)
import qualified Syntax

compile ::
  MonadError TypeError m =>
  [Syntax.Declaration] ->
  m [C.CDecl]
compile decls = do
  (kindScope, tyScope, funcs) <-
    flip evalStateT (emptyEntailState emptyTCState) $
    checkDecls mempty mempty decls
  _
  where
    checkDecls ::
      ( MonadState (s (Var Int Void)) m
      , FilterTypes s
      , HasTypeMetas s
      , forall x. HasKindMetas (s x)
      , forall x. HasSizeMetas (s x)
      , forall x. HasGlobalTheory (s x)
      , MonadError TypeError m
      ) =>
      Map Text IR.Kind ->
      Map Text (IR.TypeScheme Void) ->
      [Syntax.Declaration] ->
      m (Map Text IR.Kind, Map Text (IR.TypeScheme Void), [IR.Function])
    checkDecls kindScope tyScope ds =
      case ds of
        [] -> pure (kindScope, tyScope, [])
        d:rest ->
          case d of
            Syntax.DData (Syntax.ADT name params ctors) -> do
              (kind, axiom, size) <- checkADT kindScope name params ctors
              globalTheory %= Map.insert axiom size
              checkDecls (Map.insert name kind kindScope) tyScope rest
            Syntax.DFunc func -> do
              func' <- checkFunction kindScope tyScope func
              checkDecls
                kindScope
                (Map.insert (IR.funcName func') (IR.toTypeScheme func') tyScope)
                rest
