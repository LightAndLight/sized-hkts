{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language QuantifiedConstraints #-}
module Check.Function
  (checkFunction)
where

import Bound.Var (unvar)
import Control.Lens.Getter (use)
import Control.Lens.Indexed (ifoldlM)
import Control.Lens.Setter ((.~))
import Control.Monad.Except (MonadError)
import Control.Monad.State.Strict (evalStateT)
import Data.Bifunctor (first)
import Data.Foldable (foldlM, foldrM, traverse_)
import Data.Function ((&))
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Vector as Vector
import Data.Void (Void, absurd)

import Check.Entailment (Theory(..), freshSMeta, globalTheory, solve)
import Check.Datatype (datatypeCtors, datatypeFields)
import Check.Kind (checkKind)
import Check.TCState (emptyTCState)
import Check.Type (CheckResult(..), checkExpr, requiredConstraints, zonkExprTypes)
import Error.TypeError (TypeError(..))
import Syntax (pattern TypeM, unTypeM)
import qualified Syntax
import IR (Kind(..), TypeScheme)
import qualified IR
import Size (Size, sizeConstraintFor)
import Unify.KMeta (freshKMeta, solveKMetas)
import Unify.TMeta (solveMetas_Constraint, solveTMetas_Expr)

checkFunction ::
  MonadError TypeError m =>
  Map (IR.Constraint Void) (Size Void) ->
  Map Text IR.Fields ->
  Map Text IR.Constructor ->
  Map Text Kind ->
  Map Text (TypeScheme Void) ->
  Syntax.Function ->
  m IR.Function
checkFunction glbl fields ctors kindScope tyScope (Syntax.Function name tyArgs args retTy body) = do
  let
    initial =
      emptyTCState &
        globalTheory .~ glbl &
        datatypeFields .~ fields &
        datatypeCtors .~ ctors
  (tyArgs', constraints', body') <-
    flip evalStateT initial $ do
      tyArgKinds <- traverse (fmap KVar . const freshKMeta) tyArgs
      let args' = TypeM . fmap Right . snd <$> args
      let retTy' = TypeM $ Right <$> retTy
      checkKind
        kindScope
        (Syntax.varSpan Syntax.indexSpan Syntax.voidSpan)
        (unvar ((tyArgKinds Vector.!) . Syntax.getIndex) absurd)
        retTy'
        KType
      traverse_
        (\t ->
          checkKind
            kindScope
            (Syntax.varSpan Syntax.indexSpan Syntax.voidSpan)
            (unvar ((tyArgKinds Vector.!) . Syntax.getIndex) absurd)
            t
            KType
        )
        args'
      exprResult <-
        checkExpr
          kindScope
          (Map.insert
             name
             (IR.TypeScheme IR.OFunction
                (Vector.zip tyArgs tyArgKinds)
                mempty
                (first Just <$> args)
                retTy
             )
             tyScope
          )
          mempty
          (Syntax.varSpan Syntax.indexSpan Syntax.voidSpan)
          (Syntax.varSpan Syntax.indexSpan Syntax.voidSpan)
          (unvar ((tyArgs Vector.!) . Syntax.getIndex) absurd)
          (unvar (fst . (args Vector.!) . Syntax.getIndex) absurd)
          (unvar ((tyArgKinds Vector.!) . Syntax.getIndex) absurd)
          (unvar ((args' Vector.!) . Syntax.getIndex) absurd)
          body
          retTy'
      tyArgKinds' <- traverse (fmap (IR.substKMeta (const KType)) . solveKMetas) tyArgKinds
      constraints <- do
        reqs <- use requiredConstraints
        global <- use globalTheory
        local <- do
          -- locally, we assume each argument is sized
          argConstraints <-
            foldlM
            (\acc t -> do
               m <- freshSMeta
               pure $ Map.insert (IR.CSized $ unTypeM t) m acc
            )
            mempty
            args'
          -- and each type variable is sized
          ifoldlM
            (\ix acc k -> do
               m <- freshSMeta
               pure $
                 Map.insert
                   (Right . first (const $ Syntax.Index {- TODO -} Syntax.Unknown ix) <$> sizeConstraintFor k)
                   m
                   acc
            )
            argConstraints
            tyArgKinds'
        reqsAndRet <-
          foldrM
            (\c rest -> do
               m <- freshSMeta
               pure $ (m, c) : rest
            )
            []
            (reqs <> Set.singleton (IR.CSized $ unTypeM retTy'))
        (constraints', simplifications) <-
          solve
            kindScope
            (Syntax.varSpan Syntax.indexSpan Syntax.voidSpan)
            (unvar (Right . (tyArgs Vector.!) . Syntax.getIndex) absurd)
            (unvar ((tyArgKinds' Vector.!) . Syntax.getIndex) absurd)
            (Theory { _thGlobal = global, _thLocal = local })
            reqsAndRet
        pure . Vector.fromList $
          constraints' <>
          Map.foldrWithKey -- include all the local axioms that weren't simplified
            (\c m rest -> if Map.member m simplifications then rest else (m, c) : rest)
            []
            local
      constraints' <-
        (traverse.traverse) (either (error . ("checkFunction: unsolved meta " <>) . show) pure) =<<
        traverse (solveMetas_Constraint . snd) constraints
      body' <- zonkExprTypes =<< solveTMetas_Expr (crExpr exprResult)
      pure (Vector.zip tyArgs tyArgKinds', constraints', body')
  pure $ IR.Function name tyArgs' constraints' args retTy body'
