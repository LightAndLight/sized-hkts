{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
module Parser
  ( Parser, Parser.ParseError(..), Parser.parse, Parser.eof
  , expr
  , type_
  )
where

import Bound (Var(..))
import Control.Applicative ((<|>), many)
import Data.Functor (void)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Vector as Vector
import Text.Sage (Parser, (<?>))
import qualified Text.Sage as Parser

import Syntax (Case(..), Expr(..), Type(..))

spaces :: Parser s ()
spaces =
  void . many $
  Parser.satisfy (Parser.Predicate (== ' ') (Set.singleton $ Parser.Named "space"))

parens :: Parser s a -> Parser s a
parens = Parser.between (Parser.char '(') (Parser.char ')' <* Parser.spaces)

ident :: Parser s Text
ident = Parser.takeWhile1 Parser.pLower <?> "identifier"

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
      parens (Vector.fromList <$> commasep (expr abstract))

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

    newlines =
      many $
      Parser.satisfy
        (Parser.Predicate
          (\case; '\n' -> True; ' ' -> True; _ -> False)
          (Set.singleton $ Parser.Named "newline")
        )

    ctor = Parser.takeWhile1 (Parser.pLower <> Parser.pUpper) <?> "constructor"

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

type_ :: (Text -> Maybe a) -> Parser s (Type a)
type_ abstract = app
  where
    atom =
      TInt32 <$ Parser.symbol "int32" <* spaces <|>
      TBool <$ Parser.symbol "bool" <* spaces <|>
      TPtr <$ Parser.symbol "ptr" <* spaces <|>
      TFun . Vector.fromList <$ Parser.symbol "fun" <*>
        parens (Parser.sepBy (type_ abstract) (Parser.char ',' <* spaces)) <|>
      parens (type_ abstract) <|>
      (\i -> maybe (TName i) TVar $ abstract i) <$> ident <* spaces
    app = foldl TApp <$> atom <*> many atom
