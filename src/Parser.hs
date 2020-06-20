{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
module Parser
  ( Parser, Parser.ParseError(..), Parser.parse, Parser.eof
  , datatype
  , declaration
  , declarations
  , expr
  , function
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

import Syntax
  ( ADT(..), Ctors(..)
  , Declaration(..)
  , Function(..)
  , Case(..)
  , Expr(..)
  , Type(..)
  )

spaces :: Parser s ()
spaces =
  void . many $
  Parser.satisfy (Parser.Predicate (== ' ') (Set.singleton $ Parser.Named "space"))

newlines :: Parser s ()
newlines =
  void . many $
  Parser.satisfy
    (Parser.Predicate
      (\case; '\n' -> True; ' ' -> True; _ -> False)
      (Set.singleton $ Parser.Named "newline")
    )

parens :: Parser s a -> Parser s a
parens = Parser.between (Parser.char '(') (Parser.char ')' <* Parser.spaces)

braces :: Parser s a -> Parser s a
braces = Parser.between (Parser.char '{') (Parser.char '}' <* Parser.spaces)

angles :: Parser s a -> Parser s a
angles = Parser.between (Parser.char '<') (Parser.char '>' <* Parser.spaces)

ident :: Parser s Text
ident = Parser.takeWhile1 Parser.pLower <?> "identifier"

ctor :: Parser s Text
ctor = Parser.takeWhile1 (Parser.pLower <> Parser.pUpper) <?> "constructor"

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

datatype :: Parser s ADT
datatype =
  struct <|>
  enum
  where
    struct = do
      Parser.symbol "struct" <* Parser.char ' ' <* spaces
      tName <- ctor <* spaces
      tArgs <- Vector.fromList <$> many (ident <* spaces)
      _ <- Parser.char '=' <* spaces
      c <-
        (\n as -> Ctor n (Vector.fromList as) End) <$>
        ctor <*>
        parens (Parser.sepBy (type_ $ fmap B . (`Vector.elemIndex` tArgs)) (Parser.char ',' <* spaces))
      pure $ ADT tName tArgs c
    enum = do
      Parser.symbol "enum" <* Parser.char ' ' <* spaces
      tName <- ctor <* spaces
      tArgs <- Vector.fromList <$> many (ident <* spaces)
      cs <-
        braces $
        foldr (\(n, as) -> Ctor n (Vector.fromList as)) End <$ spaces <*>
        Parser.sepBy
          ((,) <$>
           ctor <*>
           parens
             (Parser.sepBy
                (type_ (fmap B . (`Vector.elemIndex` tArgs)))
                (Parser.char ',' <* spaces)
             )
          )
          (Parser.char ',' <* spaces)
      pure $ ADT tName tArgs cs

function :: Parser s Function
function = do
  Parser.symbol "fn" <* Parser.char ' ' <* spaces
  name <- ident
  tArgs <-
    angles $
    Vector.fromList <$>
    Parser.sepBy ident (Parser.char ',' *> spaces)
  let abstractTy = fmap B . (`Vector.elemIndex` tArgs)
  args <-
    parens $
    Vector.fromList <$>
    Parser.sepBy
      ((,) <$> ident <* spaces <* Parser.char ':' <* spaces <*> type_ abstractTy)
      (Parser.char ',' *> spaces)
  _ <- spaces <* Parser.symbol "->" <* spaces
  retTy <- type_ abstractTy
  let abstractTm v = B <$> Vector.elemIndex v (fst <$> args)
  body <- braces $ newlines *> expr abstractTm <* newlines
  pure $ Function name tArgs args retTy body

declaration :: Parser s Declaration
declaration =
  DData <$> datatype <|>
  DFunc <$> function

declarations :: Parser s [Declaration]
declarations =
  Parser.sepBy declaration newlines
