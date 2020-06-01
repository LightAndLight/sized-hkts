module Check.TypeError where

import Data.Text (Text)

import IR (Constraint, KMeta, Kind)
import Syntax (Expr)
import TCState (TMeta, TypeM)

data TypeError
  = MissingKMeta KMeta
  | MissingTMeta TMeta
  | OutOfBoundsInt32 Integer
  | TypeMismatch (TypeM Text) (TypeM Text)
  | KindMismatch Kind Kind
  | TypeOccurs TMeta (TypeM Text)
  | KindOccurs KMeta Kind
  | Can'tInfer (Expr Text)
  | NotInScope Text
  | TNotInScope Text
  | CouldNotDeduce (Constraint (Either TMeta Text))
  | Doesn'tHaveField (TypeM Text) Text
  deriving (Eq, Show)
