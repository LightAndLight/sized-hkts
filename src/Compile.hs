{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language QuantifiedConstraints #-}
{-# language ScopedTypeVariables #-}
module Compile (compile) where

import Bound.Var (Var)
import Control.Lens.Getter (use, view)
import Control.Lens.Setter ((%=), (.~))
import Control.Monad.Except (MonadError)
import Control.Monad.State (MonadState, evalState, runStateT)
import Data.Foldable (foldl')
import Data.Function ((&))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import Data.Void (Void)

import Check.Datatype (HasDatatypeCtors, HasDatatypeFields, checkADT, datatypeCtors, datatypeFields)
import Check.Entailment (HasSizeMetas, HasGlobalTheory, globalTheory)
import Check.Function (checkFunction)
import Check.TCState (emptyTCState)
import Check.TCState.FilterTypes (FilterTypes)
import Codegen (codeKinds, codeDeclarations, codeGlobalTheory)
import qualified Codegen
import qualified Codegen.C as C
import Error.TypeError (TypeError)
import qualified IR
import qualified Size.Builtins as Size
import qualified Syntax
import Unify.KMeta (HasKindMetas)
import Unify.TMeta (HasTypeMetas)

compile ::
  MonadError TypeError m =>
  [Syntax.Declaration] ->
  m [C.CDecl]
compile decls = do
  ((kindScope, _, decls'), entailState) <-
    flip runStateT (emptyTCState & globalTheory .~ Map.fromList Size.builtins) $
    checkDecls mempty mempty decls
  let
    declsMap =
      foldl'
        (\acc f -> Map.insert (IR.declOrigin f, IR.declName f) f acc)
        mempty
        decls'
    initialCode =
      Codegen.emptyCode &
        codeKinds .~ kindScope &
        codeDeclarations .~ declsMap &
        codeGlobalTheory .~ view globalTheory entailState
    code =
      flip evalState initialCode $ do
        case Map.lookup (IR.OFunction, "main") declsMap of
          Just (IR.DFunc mainFunc) -> do
            mainFunc' <- Codegen.genFunction mainFunc mempty
            ds <- Codegen.genDecls
            pure $ C.preamble <> ds <> [mainFunc']
          _ -> error "no main function"
  pure code
  where
    checkDecls ::
      ( MonadState (s (Var Int Void)) m
      , FilterTypes s
      , HasTypeMetas s
      , forall x. HasDatatypeCtors (s x)
      , forall x. HasDatatypeFields (s x)
      , forall x. HasKindMetas (s x)
      , forall x. HasSizeMetas (s x)
      , forall x. HasGlobalTheory (s x)
      , MonadError TypeError m
      ) =>
      Map Text IR.Kind ->
      Map Text (IR.TypeScheme Void) ->
      [Syntax.Declaration] ->
      m
        ( Map Text IR.Kind
        , Map Text (IR.TypeScheme Void)
        , [IR.Declaration]
        )
    checkDecls kindScope tyScope ds =
      case ds of
        [] -> pure (kindScope, tyScope, [])
        d:rest ->
          case d of
            Syntax.DData (Syntax.ADT name params ctors) -> do
              (adt, kind, axiom, size) <- checkADT kindScope name params ctors
              let ctorsDecls = IR.datatypeConstructors adt
              globalTheory %= Map.insert axiom size
              maybe
                (pure ())
                (\fs -> datatypeFields %= Map.insert name fs)
                (IR.makeDatatypeFields adt)
              (kindScope', tyScope', rest') <-
                checkDecls
                  (Map.insert name kind kindScope)
                  (foldl'
                    (\acc ctor ->
                      Map.insert
                        (IR.ctorName ctor)
                        (IR.constructorToTypeScheme ctor)
                        acc
                    )
                    tyScope
                    ctorsDecls
                  )
                  rest
              pure
                ( kindScope'
                , tyScope'
                , IR.DData adt : foldr ((:) . IR.DCtor) rest' ctorsDecls
                )
            Syntax.DFunc func -> do
              global <- use globalTheory
              fields <- use datatypeFields
              ctors <- use datatypeCtors
              func' <- checkFunction global fields ctors kindScope tyScope func
              (kindScope', tyScope', rest') <-
                checkDecls
                  kindScope
                  (Map.insert
                    (IR.funcName func')
                    (IR.functionToTypeScheme func')
                    tyScope
                  )
                  rest
              pure (kindScope', tyScope', IR.DFunc func' : rest')
