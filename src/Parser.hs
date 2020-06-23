{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language ScopedTypeVariables #-}
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
  ( Index(..), Span(..)
  , ADT(..), Ctors(..)
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
parens = Parser.between (Parser.char '(') (Parser.char ')')

braces :: Parser s a -> Parser s a
braces = Parser.between (Parser.char '{') (Parser.char '}')

angles :: Parser s a -> Parser s a
angles = Parser.between (Parser.char '<') (Parser.char '>')

ident :: Parser s Text
ident = Parser.takeWhile1 (Parser.pLower <> Parser.pUpper) <?> "identifier"

expr :: forall s a. (Parser.Span -> Text -> Maybe a) -> Parser s (Expr a)
expr abstract =
  match <|>
  deref
  where
    bool :: Parser s (Expr a)
    bool =
      (\(sp, _) -> BTrue $ Known sp) <$> Parser.spanned (Parser.symbol "true") <* spaces <|>
      (\(sp, _) -> BFalse $ Known sp) <$> Parser.spanned (Parser.symbol "false") <* spaces

    new =
      (\(sp, e) -> New (Known sp) e) <$>
      Parser.spanned
      (Parser.symbol "new" *> Parser.char '[' *>
       expr abstract <* Parser.char ']'
      ) <* spaces

    field =
      Parser.takeWhile1 Parser.pDigit <|>
      Parser.takeWhile1 Parser.pLower

    commasep p = Parser.sepBy p (Parser.char ',' *> spaces)

    args =
      parens (Vector.fromList <$> commasep (expr abstract))

    projectOrCall =
      (\(sp, (z, as)) ->
         foldl (\acc -> either (Project (Known sp) acc) (Call (Known sp) acc)) z as
      ) <$>
      (Parser.spanned $
       (,) <$>
       atom <*>
       many
         (Left <$ Parser.char '.' <*> field <* spaces <|>
          Right <$> args <* spaces
         )
      )

    deref =
      (\(sp, e) -> Deref (Known sp) e) <$> Parser.spanned (Parser.char '*' *> deref) <|>
      projectOrCall

    number =
      (\(sp, x) -> Number (Known sp) x) <$>
      (Parser.spanned $
       (negate <$ Parser.char '-' <|> pure id) <*>
       Parser.decimal
      ) <* spaces

    atom =
      bool <|>
      new <|>
      number <|>
      (\(sp, i) -> maybe (Name (Known sp) i) Var $ abstract sp i) <$> Parser.spanned ident <* spaces <|>
      parens (expr abstract) <* spaces

    case_ = do
      (sp, (c, as)) <-
        Parser.spanned $
        (,) <$> ident <*> parens (Vector.fromList <$> commasep ident)
      _ <- spaces *> Parser.symbol "=>" *> spaces
      e <- expr (\s n -> B . Index (Known s) <$> Vector.findIndex (n ==) as <|> F <$> abstract s n)
      pure $ Case (Known sp) c as e

    match =
      (\(sp, (e, bs)) -> Match (Known sp) e bs) <$>
      (Parser.spanned $
       (,) <$ Parser.symbol "match" <* spaces <*>
       deref <* spaces <*>
       Parser.between
         (Parser.char '{' *> newlines)
         (newlines *> Parser.char '}')
         (Vector.fromList <$> Parser.sepBy case_ (Parser.char ',' <* newlines))
      )

type_ :: forall s a. (Parser.Span -> Text -> Maybe a) -> Parser s (Type a)
type_ abstract = snd <$> self
  where
    self = app

    atom :: Parser s (Type a)
    atom =
      (\(sp, _) -> TInt32 $ Known sp) <$> Parser.spanned (Parser.symbol "int32") <* spaces <|>
      (\(sp, _) -> TBool $ Known sp) <$> Parser.spanned (Parser.symbol "bool") <* spaces <|>
      (\(sp, _) -> TPtr $ Known sp) <$> Parser.spanned (Parser.symbol "ptr") <* spaces <|>
      (\(sp, ts) -> TFun (Known sp) $ Vector.fromList ts) <$>
      Parser.spanned
        (Parser.symbol "fun" *>
         parens (Parser.sepBy (type_ abstract) (Parser.char ',' <* spaces)) <*
         spaces
        ) <|>
      parens (type_ abstract) <|>
      (\(sp, i) -> maybe (TName (Known sp) i) TVar $ abstract sp i) <$> Parser.spanned ident <* spaces

    app =
      foldl
        (\(spl, l) (spr, r) -> let sp = spl <> spr in (sp, TApp (Known sp) l r)) <$>
        Parser.spanned atom <*>
        many (Parser.spanned atom)

datatype :: Parser s ADT
datatype =
  struct <|>
  enum
  where
    struct = do
      Parser.symbol "struct" <* Parser.char ' ' <* spaces
      tName <- ident <* spaces
      tArgs <- Vector.fromList <$> many (ident <* spaces)
      _ <- Parser.char '=' <* spaces
      c <-
        (\n as -> Ctor n (Vector.fromList as) End) <$>
        ident <*>
        parens
          (Parser.sepBy
             (type_ $ \sp v -> B . Index (Known sp) <$> Vector.elemIndex v tArgs)
             (Parser.char ',' <* spaces)
          )
      pure $ ADT tName tArgs c
    enum = do
      Parser.symbol "enum" <* Parser.char ' ' <* spaces
      tName <- ident <* spaces
      tArgs <- Vector.fromList <$> many (ident <* spaces)
      cs <-
        braces $
        foldr (\(n, as) -> Ctor n (Vector.fromList as)) End <$ spaces <*>
        Parser.sepBy
          ((,) <$>
           ident <*>
           parens
             (Parser.sepBy
               (type_ $ \sp v -> B . Index (Known sp) <$> Vector.elemIndex v tArgs)
               (Parser.char ',' <* spaces)
             ) <*
            spaces
          )
          (Parser.char ',' <* spaces)
      pure $ ADT tName tArgs cs

function :: Parser s Function
function = do
  Parser.symbol "fn" <* Parser.char ' ' <* spaces
  name <- ident
  tArgs <-
    angles
      (Vector.fromList <$>
      Parser.sepBy ident (Parser.char ',' *> spaces)
      ) <|>
    pure mempty
  let abstractTy sp v = B . Index (Known sp) <$> Vector.elemIndex v tArgs
  args <-
    parens $
    Vector.fromList <$>
    Parser.sepBy
      ((,) <$> ident <* spaces <* Parser.char ':' <* spaces <*> type_ abstractTy)
      (Parser.char ',' *> spaces)
  _ <- spaces <* Parser.symbol "->" <* spaces
  retTy <- type_ abstractTy
  let abstractTm sp v = B . Index (Known sp) <$> Vector.elemIndex v (fst <$> args)
  body <- braces $ newlines *> expr abstractTm <* newlines
  pure $ Function name tArgs args retTy body

declaration :: Parser s Declaration
declaration =
  DData <$> datatype <|>
  DFunc <$> function

declarations :: Parser s [Declaration]
declarations =
  Parser.sepBy declaration newlines
