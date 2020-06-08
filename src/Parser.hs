module Parser () where

import Data.Void (Void)
import Text.Sage (Parser)

import Syntax (Expr(..), Type(..))

expr :: Parser s (Expr Void)
expr = _
