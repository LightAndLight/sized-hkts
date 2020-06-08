{-# language OverloadedStrings #-}
module Parser () where

import Control.Applicative ((<|>), many, optional)
import Data.Foldable (foldl')
import Data.Void (Void)
import Text.Sage (Parser, (<?>))
import qualified Text.Sage as Parser

import Syntax (Expr(..), Type(..))

expr :: Parser s (Expr Void)
expr = undefined
  where
    bool =
      BTrue <$ Parser.text "true" <?> "true" <|>
      BFalse <$ Parser.text "false" <?> "false"

    new =
      New <$ Parser.text "new" <* Parser.char '[' <*>
      expr <* Parser.char ']'

    project =
      foldl Project <$> atom <*> many field

    deref =
      maybe id (\() -> Deref) <$> optional (Parser.char '*') <*>
      project

    number =
      (\f -> Number . f) <$>
      (negate <$ Parser.char '-' <|> pure id) <*>
      Parser.decimal

    atom =
      bool <|>
      new <|>
      number

    field = _
