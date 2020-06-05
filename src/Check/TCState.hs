{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language FunctionalDependencies, MultiParamTypeClasses, TypeFamilies #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
module Check.TCState
  ( TCState
  , emptyTCState
  , tcsKindMeta
  , tcsKindSolutions
  , tcsTypeMeta
  , tcsTypeMetaKinds
  , tcsTypeSolutions
  , tcsConstraints
  , tcsGlobalTheory
  )
where

import Control.Lens.Getter ((^.))
import Control.Lens.TH (makeLenses)
import Data.Foldable (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Void (Void)

import Check.Datatype (HasDatatypeCtors(..), HasDatatypeFields(..))
import Check.Entailment (HasGlobalTheory(..), HasSizeMetas(..), SMeta(..))
import Check.TCState.FilterTypes (FilterTypes(..))
import Check.Type (HasConstraints(..))
import IR (Constraint, KMeta(..), Kind(..))
import qualified IR
import Size (Size)
import Syntax (TMeta(..), TypeM)
import Unify.KMeta (HasKindMetas(..))
import Unify.TMeta (HasTypeMetas(..))

data TCState ty
  = TCState
  { _tcsKindMeta :: KMeta
  , _tcsKindSolutions :: Map KMeta Kind
  , _tcsTypeMeta :: TMeta
  , _tcsTypeMetaKinds :: Map TMeta Kind
  , _tcsTypeSolutions :: Map TMeta (TypeM ty)
  , _tcsConstraints :: Set (Constraint (Either TMeta ty))
  , _tcsSizeMeta :: SMeta
  , _tcsGlobalTheory :: Map (Constraint Void) (Size Void)
  , _tcsDatatypeFields :: Map Text IR.Fields
  , _tcsDatatypeCtors :: Map Text IR.Constructor
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
  , _tcsSizeMeta = SMeta 0
  , _tcsDatatypeFields = mempty
  , _tcsDatatypeCtors = mempty
  }

instance HasGlobalTheory (TCState ty) where
  globalTheory = tcsGlobalTheory

instance HasSizeMetas (TCState ty) where
  nextSMeta  = tcsSizeMeta

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

instance HasDatatypeFields (TCState ty) where
  datatypeFields = tcsDatatypeFields

instance HasDatatypeCtors (TCState ty) where
  datatypeCtors = tcsDatatypeCtors
