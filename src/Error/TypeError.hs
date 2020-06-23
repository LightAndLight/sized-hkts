module Error.TypeError where

import Data.Text (Text)
import qualified Data.Text as Text

import IR (Constraint, KMeta, Kind)
import Syntax (Span, TMeta, TypeM)

data TypeError
  = MissingKMeta KMeta
  | MissingTMeta TMeta
  | OutOfBoundsInt32 !Span
  | TypeMismatch !Span (TypeM Text) (TypeM Text)
  | KindMismatch !Span Kind Kind
  | TypeOccurs !Span TMeta (TypeM Text)
  | KindOccurs !Span KMeta Kind
  | Can'tInfer !Span
  | NotInScope !Span
  | TNotInScope !Span
  | CouldNotDeduce {- TODO: !Span -} (Constraint (Either TMeta Text))
  | Doesn'tHaveField !Span (TypeM Text) Text
  | CtorNotInScope !Span
  | CtorArityMismatch !Span Int Int
  | MatchingOnStruct !Span
  deriving (Eq, Show)

renderTyName :: Either Int Text -> Text
renderTyName = either (Text.pack . ("#" <>) . show) id

typeMismatch :: (ty -> Either Int Text) -> Span -> TypeM ty -> TypeM ty -> TypeError
typeMismatch tyNames sp expected actual =
  TypeMismatch sp (renderTyName . tyNames <$> expected) (renderTyName . tyNames <$> actual)
