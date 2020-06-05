module Error.TypeError where

import Data.Text (Text)
import qualified Data.Text as Text

import IR (Constraint, KMeta, Kind)
import Syntax (Expr, TMeta, TypeM)

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
  | CtorNotInScope Text
  | CtorArityMismatch Text Int Int
  deriving (Eq, Show)

renderTyName :: Either Int Text -> Text
renderTyName = either (Text.pack . ("#" <>) . show) id

typeMismatch :: (ty -> Either Int Text) -> TypeM ty -> TypeM ty -> TypeError
typeMismatch tyNames expected actual =
  TypeMismatch (renderTyName . tyNames <$> expected) (renderTyName . tyNames <$> actual)
