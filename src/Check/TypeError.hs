module Check.TypeError where

import Data.Text (Text)

import IR (KMeta, Kind)
import Syntax (Expr, WordSize)
import TCState (TMeta, TypeM)

data TypeError
  = MissingKMeta KMeta
  | MissingTMeta TMeta
  | NotNumeric (TypeM Text)
  | OutOfBoundsUnsigned WordSize Integer
  | OutOfBoundsSigned WordSize Integer
  | TypeMismatch (TypeM Text) (TypeM Text)
  | KindMismatch Kind Kind
  | TypeOccurs TMeta (TypeM Text)
  | KindOccurs KMeta Kind
  | Can'tInfer (Expr Text)
  | NotInScope Text
  | TNotInScope Text
  deriving (Eq, Show)
