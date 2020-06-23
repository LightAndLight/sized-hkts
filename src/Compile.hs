{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language QuantifiedConstraints #-}
{-# language ScopedTypeVariables #-}
module Compile
  ( CompileError(..)
  , SyntaxError(..)
  , parse
  , compile
  , parseAndCompile
  )
where

import Bound.Var (Var)
import Control.Lens.Getter (use, view)
import Control.Lens.Setter ((%=), (.~), (<>=))
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State.Strict (MonadState, evalStateT, runStateT)
import Data.Foldable (foldl')
import Data.Function ((&))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text.Lazy as Lazy
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import Data.Void (Void)
import Text.Diagnostic (Diagnostic(..), Position(..), Report, render, defaultConfig, emit)
import Text.Diagnostic.Sage (parseError)
import Text.Sage (spanStart, spanLength)

import Check.Datatype (HasDatatypeCtors, HasDatatypeFields, checkADT, datatypeCtors, datatypeFields)
import Check.Entailment (HasSizeMetas, HasGlobalTheory, globalTheory)
import Check.Function (checkFunction)
import Check.TCState (emptyTCState)
import Check.TCState.FilterTypes (FilterTypes)
import Codegen (codeKinds, codeDatatypeCtors, codeDeclarations, codeGlobalTheory)
import qualified Codegen
import qualified Codegen.C as C
import Error.TypeError (TypeError(..))
import qualified IR
import qualified Parser
import qualified Size.Builtins as Size
import Syntax (Index, Span(..))
import qualified Syntax
import Unify.KMeta (HasKindMetas)
import Unify.TMeta (HasTypeMetas)

data SyntaxError
  = ParseError Parser.ParseError

renderSyntaxError :: Text -> Text -> SyntaxError -> Lazy.Text
renderSyntaxError fileName input (ParseError err) =
  render defaultConfig fileName input (parseError err)

emitSpan :: Span -> Builder -> Report
emitSpan sp msg =
  case sp of
    Unknown ->
      emit
        (Offset 0)
        Caret
        (msg <> " (location unknown)")
    Known sp' ->
      emit
        (Offset $ spanStart sp')
        (Span $ spanLength sp')
        msg

prettyTypeM :: (a -> Text) -> Syntax.TypeM a -> Text
prettyTypeM f = Syntax.prettyType (either Syntax.prettyTMeta f) . Syntax.unTypeM

typeError :: TypeError -> Report
typeError err =
  case err of
    MissingKMeta k -> error $ "internal error: missing kind meta " <> show k
    MissingTMeta t -> error $ "internal error: missing type meta " <> show t
    OutOfBoundsInt32 sp ->
      emitSpan sp "out of bounds for 32-bit int"
    TypeMismatch sp expected actual ->
      emitSpan sp $
      "expected type '" <>
      Builder.fromText (prettyTypeM id expected) <>
      "', got '" <>
      Builder.fromText (prettyTypeM id actual) <>
      "'"
    KindMismatch sp expected actual ->
      emitSpan sp $
      "expected kind '" <>
      Builder.fromText (IR.prettyKind expected) <>
      "', got '" <>
      Builder.fromText (IR.prettyKind actual) <>
      "'"
    TypeOccurs sp v t ->
      emitSpan sp $
      "cannot equate types '" <>
      Builder.fromText (Syntax.prettyTMeta v) <>
      "', and '" <>
      Builder.fromText (prettyTypeM id t) <>
      "'"
    KindOccurs sp v k ->
      emitSpan sp $
      "cannot equate kinds '" <>
      Builder.fromText (IR.prettyKMeta v) <>
      "', and '" <>
      Builder.fromText (IR.prettyKind k) <>
      "'"
    Can'tInfer sp -> emitSpan sp "can't infer type"
    NotInScope sp -> emitSpan sp "variable not in scope"
    TNotInScope sp -> emitSpan sp "type not in scope"
    CouldNotDeduce c ->
      emitSpan {- TODO -}Unknown $
      "could not deduce " <>
      Builder.fromText (IR.prettyConstraint (Right . either Syntax.prettyTMeta id) c)
    Doesn'tHaveField sp t f ->
      emitSpan sp $
      "type '" <>
      Builder.fromText (prettyTypeM id t) <>
      "' has no field \"" <>
      Builder.fromText f <>
      "\""
    CtorNotInScope sp ->
      emitSpan sp "constructor not in scope"
    CtorArityMismatch sp expected actual ->
      emitSpan sp $
      "expected " <>
      Builder.fromString (show expected) <>
      " arguments, got " <>
      Builder.fromString (show actual)
    MatchingOnStruct sp ->
      emitSpan sp "can't pattern match on struct"

data CompileError
  = TypeError TypeError
  | MissingMainFunction
  deriving (Eq, Show)

compileError :: CompileError -> Report
compileError err =
  case err of
    TypeError e -> typeError e
    MissingMainFunction -> emitSpan Unknown "missing main function"

renderCompileError :: Text -> Text -> CompileError -> Lazy.Text
renderCompileError fileName input = render defaultConfig fileName input . compileError

parseAndCompile ::
  MonadError Lazy.Text m =>
  Text -> -- file name
  Text -> -- input
  m [C.CDecl]
parseAndCompile fileName input =
  case parse input of
    Left err -> throwError $ renderSyntaxError fileName input err
    Right decls ->
      case compile decls of
        Left err -> throwError $ renderCompileError fileName input err
        Right res -> pure res

parse ::
  MonadError SyntaxError m =>
  Text ->
  m [Syntax.Declaration]
parse input =
  case Parser.parse (Parser.declarations <* Parser.eof) input of
    Left err -> throwError $ ParseError err
    Right decls -> pure decls

compile ::
  MonadError CompileError m =>
  [Syntax.Declaration] ->
  m [C.CDecl]
compile decls = do
  ((kindScope, _, decls'), tcState) <-
    either (throwError . TypeError) pure .
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
        codeGlobalTheory .~ view globalTheory tcState &
        codeDatatypeCtors .~ view datatypeCtors tcState
  code <-
    flip evalStateT initialCode $
    case Map.lookup (IR.OFunction, "main") declsMap of
      Just (IR.DFunc mainFunc) -> do
        mainFunc' <- Codegen.genFunction mainFunc mempty
        ds <- Codegen.genDecls
        pure $ C.preamble <> ds <> [mainFunc']
      _ -> throwError MissingMainFunction
  pure code
  where
    checkDecls ::
      ( MonadState (s (Var Index Void)) m
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
              datatypeCtors <>= foldl' (\acc c -> Map.insert (IR.ctorName c) c acc) mempty ctorsDecls
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
