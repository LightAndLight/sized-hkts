{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language FunctionalDependencies, MultiParamTypeClasses, TypeFamilies #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
module TCState
  ( TCState
  , emptyTCState
  , tcsKindMeta
  , tcsKindSolutions
  , tcsTypeMeta
  , tcsTypeMetaKinds
  , tcsTypeSolutions
  , tcsConstraints
  , tcsGlobalTheory
  , HasConstraints(..)
  , FilterTypes(..), mapTypes
  , HasDatatypeFields(..)
  , getFieldType
  )
where

import Bound.Var (Var(..))
import Control.Lens.Getter ((^.), uses)
import Control.Lens.Lens (Lens')
import Control.Lens.TH (makeLenses)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState)
import Data.Foldable (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Vector as Vector
import Data.Void (Void)

import Error.TypeError (TypeError(..))
import IR (Constraint, KMeta(..), Kind(..))
import qualified IR
import Size (Size)
import Syntax (TMeta(..), Type(..), TypeM)
import Unify.Kind (HasKindMetas(..))
import Unify.TMeta (HasTypeMetas(..))

data TCState ty
  = TCState
  { _tcsKindMeta :: KMeta
  , _tcsKindSolutions :: Map KMeta Kind
  , _tcsTypeMeta :: TMeta
  , _tcsTypeMetaKinds :: Map TMeta Kind
  , _tcsTypeSolutions :: Map TMeta (TypeM ty)
  , _tcsConstraints :: Set (Constraint (Either TMeta ty))
  , _tcsGlobalTheory :: Map (Constraint Void) (Size Void)
  , _tcsDatatypeFields :: Map Text IR.Fields
  }
makeLenses ''TCState

emptyTCState :: Ord ty => TCState ty
emptyTCState =
  TCState
  { _tcsKindMeta = KMeta 0
  , _tcsKindSolutions = mempty
  , _tcsTypeMeta = TMeta 0
  , _tcsTypeMetaKinds = mempty
  , _tcsTypeSolutions = mempty
  , _tcsConstraints = mempty
  , _tcsGlobalTheory = mempty
  , _tcsDatatypeFields = mempty
  }

class FilterTypes s where
  filterTypes :: Ord ty' => (ty -> Maybe ty') -> s ty -> s ty'

mapTypes :: (FilterTypes s, Ord ty') => (ty -> ty') -> s ty -> s ty'
mapTypes f = filterTypes (Just . f)

class HasConstraints s where
  requiredConstraints :: Lens' (s ty) (Set (Constraint (Either TMeta ty)))

instance HasConstraints TCState where
  requiredConstraints = tcsConstraints

instance HasTypeMetas TCState where
  nextTMeta = tcsTypeMeta
  tmetaKinds = tcsTypeMetaKinds
  tmetaSolutions = tcsTypeSolutions

instance HasKindMetas (TCState ty) where
  nextKMeta = tcsKindMeta
  kmetaSolutions = tcsKindSolutions

instance FilterTypes TCState where
  filterTypes f tcs =
    let
      (tmetas, sols') =
        Map.foldrWithKey
          (\k a (ms, ss) ->
            case traverse f a of
              Nothing -> (k:ms, ss)
              Just a' -> (ms, Map.insert k a' ss)
          )
          ([], mempty)
          (tcs ^. tcsTypeSolutions)
      kinds' = foldl' (flip Map.delete) (tcs ^. tcsTypeMetaKinds) tmetas
      constraints' =
        foldr
          (\c ->
             case traverse (either (Just . Left) (fmap Right . f)) c of
               Nothing -> id
               Just c' -> Set.insert c'
          )
          mempty
          (tcs ^. tcsConstraints)
    in
      tcs
      { _tcsTypeMetaKinds = kinds'
      , _tcsTypeSolutions = sols'
      , _tcsConstraints = constraints'
      }

class HasDatatypeFields s where
  datatypeFields :: Lens' s (Map Text IR.Fields)

instance HasDatatypeFields (TCState ty) where
  datatypeFields = tcsDatatypeFields

getFieldType ::
  ( MonadState s m, HasDatatypeFields s
  , MonadError TypeError m
  ) =>
  Text ->
  IR.Projection ->
  m (Maybe (Type (Var Int Void)))
getFieldType tyName prj = do
  m_fs <- uses datatypeFields $ Map.lookup tyName
  case m_fs of
    Nothing -> throwError $ TNotInScope tyName
    Just fs ->
      pure $ case prj of
        IR.Numeric ix ->
          case fs of
            IR.Unnamed fs' -> Just $ fs' Vector.! fromIntegral ix
            _ -> Nothing
        IR.Field n ->
          case fs of
            IR.Named fs' -> Map.lookup n fs'
            _ -> Nothing
