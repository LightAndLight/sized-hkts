{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language TypeApplications #-}
module Check.Function
  (checkFunction)
where

import Bound.Var (unvar)
import Control.Lens.Getter (use)
import Control.Monad.Except (MonadError)
import Control.Monad.State (evalStateT)
import Data.Foldable (foldlM, foldrM, traverse_)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Vector as Vector
import Data.Void (Void, absurd)

import Check.Entailment (Theory(..), emptyEntailState, freshSMeta, globalTheory, solve)
import Check.Kind (checkKind)
import Check.TypeError (TypeError(..))
import qualified Syntax
import IR (Kind(..), TypeScheme)
import qualified IR
import TCState
  ( pattern TypeM, unTypeM
  , emptyTCState
  , freshKMeta
  , requiredConstraints
  , solveMetas_Constraint
  , solveKMetas
  )
import Typecheck (CheckResult(..), checkExpr, zonkExprTypes)

checkFunction ::
  MonadError TypeError m =>
  Map Text Kind ->
  Map Text (TypeScheme Void) ->
  Syntax.Function ->
  m IR.Function
checkFunction kindScope tyScope (Syntax.Function name tyArgs args retTy body) = do
  (tyArgs', constraints', body') <-
    flip evalStateT (emptyEntailState emptyTCState) $ do
      tyArgKinds <- traverse (fmap KVar . const freshKMeta) tyArgs
      let args' = TypeM . fmap Right . snd <$> args
      let retTy' = TypeM $ Right <$> retTy
      checkKind kindScope (unvar (tyArgKinds Vector.!) absurd) retTy' KType
      traverse_ (\t -> checkKind kindScope (unvar (tyArgKinds Vector.!) absurd) t KType) args'
      exprResult <-
        checkExpr
          kindScope
          tyScope
          mempty
          (unvar (tyArgs Vector.!) absurd)
          (unvar (fst . (args Vector.!)) absurd)
          (unvar (tyArgKinds Vector.!) absurd)
          (unvar (args' Vector.!) absurd)
          body
          retTy'
      tyArgKinds' <- traverse (fmap (IR.substKMeta (const KType)) . solveKMetas) tyArgKinds
      constraints <- do
        reqs <- use requiredConstraints
        global <- use globalTheory
        local <-
          foldlM
            (\acc t -> do
               m <- freshSMeta
               pure $ Map.insert (IR.CSized $ unTypeM t) m acc
            )
            mempty
            args'
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
            (unvar (Right . (tyArgs Vector.!)) absurd)
            (unvar (tyArgKinds' Vector.!) absurd)
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
      body' <- zonkExprTypes $ crExpr exprResult
      pure (Vector.zip tyArgs tyArgKinds', constraints', body')
  pure $ IR.Function name tyArgs' constraints' args retTy body'