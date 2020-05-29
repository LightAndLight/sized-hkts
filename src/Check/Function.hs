{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
module Check.Function
  (checkFunctionBody, checkFunction)
where

import Bound.Var (Var(..), unvar)
import Control.Lens.Getter (use)
import Control.Monad.Except (MonadError)
import Control.Monad.State (evalStateT, runStateT, get)
import Data.Foldable (foldlM, foldrM)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Void (Void, absurd)

import Check.Entailment (Theory(..), emptyEntailState, freshSMeta, globalTheory, solve)
import Check.Kind (checkKind)
import Check.TypeError (TypeError(..))
import Syntax (Type)
import qualified Syntax
import IR (Kind(..), TypeScheme)
import qualified IR
import TCState
  ( TypeM, pattern TypeM
  , TCState, emptyTCState
  , filterTypes, mapTypes
  , getKMeta
  , freshKMeta
  , requiredConstraints
  , solveMetas_Constraint
  )
import Typecheck (CheckResult(..), checkExpr, zonkExprTypes)

checkFunctionBody ::
  ( MonadError TypeError m
  , Ord ty
  ) =>
  TCState ty ->
  Map Text Kind ->
  Map Text (TypeScheme Void) ->
  (ty -> Text) ->
  (tm -> Text) ->
  (ty -> Kind) ->
  (tm -> TypeM ty) ->
  Text ->
  (TypeScheme ty -> TypeScheme Void) ->
  Vector (Type ty) ->
  Syntax.FunctionBody ty tm ->
  m (IR.FunctionBody ty tm, TCState ty)
checkFunctionBody tcstate kindScope tyScope tyNames argNames kinds types name mkScheme argTypes fb =
  case fb of
    Syntax.Forall tyName rest -> do
      (meta, tcstate') <- runStateT freshKMeta tcstate
      (rest', tcstate'') <-
        checkFunctionBody
          (mapTypes F tcstate')
          kindScope
          tyScope
          (unvar (\() -> tyName) tyNames)
          argNames
          (unvar (\() -> KVar meta) kinds)
          (fmap F . types)
          name
          (mkScheme . IR.SForall tyName (KVar meta))
          ((fmap.fmap) F argTypes)
          rest
      m_k <- evalStateT (getKMeta meta) tcstate''
      case m_k of
        Nothing -> error $ "unsolved: " <> show meta
        Just k ->
          pure
            ( IR.Forall tyName k rest'
            , filterTypes (unvar (\() -> Nothing) Just) tcstate''
            )
    Syntax.Arg argName argTy rest -> do
      let argTy' = TypeM $ Right <$> argTy
      ((), tcstate') <-
        flip runStateT tcstate $
        checkKind kindScope kinds argTy' KType
      (rest', tcstate'') <-
        checkFunctionBody
          tcstate'
          kindScope
          tyScope
          tyNames
          (unvar (\() -> argName) argNames)
          kinds
          (unvar (\() -> argTy') types)
          name
          mkScheme
          (Vector.snoc argTypes argTy)
          rest
      pure (IR.Arg argName argTy rest', tcstate'')
    Syntax.Done retTy expr ->
      flip runStateT tcstate $ do
        exprResult <-
          checkExpr
            kindScope
            (Map.insert name (mkScheme $ IR.SDone mempty argTypes retTy) tyScope) -- for recursive calls
            mempty
            tyNames
            argNames
            kinds
            types
            expr
            (TypeM $ Right <$> retTy)
        expr' <- zonkExprTypes (crExpr exprResult)
        constraints <-
          Set.insert (IR.CSized $ Right <$> retTy) <$>
          use requiredConstraints
        constraints' <- do
          s <- get
          flip evalStateT (emptyEntailState s) $ do
            csWithEvidence <-
              foldrM
                (\c rest -> do
                   meta <- freshSMeta
                   pure $ (meta, c) : rest
                )
                []
                constraints
            global <- use globalTheory
            local <-
              foldlM
                (\acc t -> do
                   meta <- freshSMeta
                   pure $ Map.insert (IR.CSized $ Right <$> t) meta acc
                )
                mempty
                argTypes
            (csWithEvidence', simplifications) <-
              solve
                kindScope
                (Right . tyNames)
                kinds
                (Theory
                 { _thGlobal = global
                 , _thLocal = local
                 }
                )
                csWithEvidence
            foldrM
              (\(_, c) rest -> do
                 c' <- solveMetas_Constraint c
                 case traverse (either (const Nothing) Just) c' of
                   Nothing -> error $ "checkFunctionBody: found meta"
                   Just c'' -> pure $ c'' : rest
              )
              []
              (Map.foldrWithKey
                 -- local assumptions should be present in the final output, unless they were
                 -- simplified away
                 (\c m acc -> if m `Map.member` simplifications then acc else (m, c) : acc)
                 csWithEvidence'
                 local
              )
        pure (foldr IR.Constraint (IR.Done retTy expr') constraints')

checkFunction ::
  MonadError TypeError m =>
  Map Text Kind ->
  Map Text (TypeScheme Void) ->
  Syntax.Function ->
  m IR.Function
checkFunction kindScope tyScope (Syntax.Function name body) = do
  (body', _) <-
    checkFunctionBody
      emptyTCState
      kindScope
      tyScope
      absurd
      absurd
      absurd
      absurd
      name
      id
      mempty
      body
  pure $ IR.Function name body'
