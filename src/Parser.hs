{-# language OverloadedStrings #-}
module Parser (Parser, Parser.ParseError(..), Parser.parse, Parser.eof, expr) where

import Control.Applicative ((<|>), many)
import qualified Data.Vector as Vector
import Data.Void (Void)
import Text.Sage (Parser, (<?>))
import qualified Text.Sage as Parser

import Syntax (Expr(..))

expr :: Parser s (Expr Void)
expr = deref
  where
    bool =
      BTrue <$ Parser.symbol "true" <|>
      BFalse <$ Parser.symbol "false"

    new =
      New <$ Parser.symbol "new" <* Parser.char '[' <*>
      expr <* Parser.char ']'

    field =
      Parser.takeWhile1 Parser.pDigit <|>
      Parser.takeWhile1 Parser.pLower

    args =
      Parser.between
        (Parser.char '(')
        (Parser.char ')')
        (Vector.fromList <$> Parser.sepBy expr (Parser.char ',' *> spaces))

    projectOrCall =
      foldl (\acc -> either (Project acc) (Call acc)) <$>
      atom <*>
      many (Left <$ Parser.char '.' <*> field <|> Right <$> args)

    deref =
      Deref <$ Parser.char '*' <*> deref <|>
      projectOrCall

    number =
      (\f -> Number . f) <$>
      (negate <$ Parser.char '-' <|> pure id) <*>
      Parser.decimal

    spaces = Parser.takeWhile1 ((== ' '), "space")

    ident = Name <$> Parser.takeWhile1 Parser.pLower <?> "identifier"

    atom =
      bool <|>
      new <|>
      number <|>
      ident
