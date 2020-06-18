{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
module Parser (Parser, Parser.ParseError(..), Parser.parse, Parser.eof, expr) where

import Bound (Var(..))
import Control.Applicative ((<|>), many)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Vector as Vector
import Text.Sage (Parser, (<?>))
import qualified Text.Sage as Parser

import Syntax (Case(..), Expr(..))

expr :: (Text -> Maybe a) -> Parser s (Expr a)
expr abstract =
  match <|>
  deref
  where
    bool =
      BTrue <$ Parser.symbol "true" <* spaces <|>
      BFalse <$ Parser.symbol "false" <* spaces

    new =
      New <$ Parser.symbol "new" <* Parser.char '[' <*>
      expr abstract <* Parser.char ']' <* spaces

    field =
      Parser.takeWhile1 Parser.pDigit <|>
      Parser.takeWhile1 Parser.pLower

    commasep p = Parser.sepBy p (Parser.char ',' *> spaces)

    args =
      Parser.between
        (Parser.char '(')
        (Parser.char ')')
        (Vector.fromList <$> commasep (expr abstract))

    projectOrCall =
      foldl (\acc -> either (Project acc) (Call acc)) <$>
      atom <*>
      many
        (Left <$ Parser.char '.' <*> field <* spaces <|>
         Right <$> args <* spaces
        )

    deref =
      Deref <$ Parser.char '*' <*> deref <|>
      projectOrCall

    number =
      (\f -> Number . f) <$>
      (negate <$ Parser.char '-' <|> pure id) <*>
      Parser.decimal <* spaces

    spaces =
      many $
      Parser.satisfy (Parser.Predicate (== ' ') (Set.singleton $ Parser.Named "space"))

    newlines =
      many $
      Parser.satisfy
        (Parser.Predicate
          (\case; '\n' -> True; ' ' -> True; _ -> False)
          (Set.singleton $ Parser.Named "newline")
        )

    ident = Parser.takeWhile1 Parser.pLower <?> "identifier"

    ctor = Parser.takeWhile1 (Parser.pLower <> Parser.pUpper) <?> "constructor"

    parens = Parser.between (Parser.char '(') (Parser.char ')')

    atom =
      bool <|>
      new <|>
      number <|>
      (\i -> maybe (Name i) Var $ abstract i) <$> ident <* spaces <|>
      parens (expr abstract) <* spaces

    case_ = do
      c <- ctor
      as <- parens (Vector.fromList <$> commasep ident)
      _ <- spaces *> Parser.symbol "=>" *> spaces
      e <- expr (\n -> B <$> Vector.findIndex (n ==) as <|> F <$> abstract n)
      pure $ Case c as e

    match =
      Match <$ Parser.symbol "match" <* spaces <*>
      deref <* spaces <*>
      Parser.between
        (Parser.char '{' *> newlines)
        (Parser.char '}')
        (Vector.fromList <$>
         Parser.sepBy case_ (Parser.char ',' <* newlines)
        )
