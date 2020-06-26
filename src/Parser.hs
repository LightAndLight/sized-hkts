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
import Data.Vector (Vector)
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

expr :: forall s a. Parser s ((Parser.Span -> Text -> Maybe a) -> Expr a)
expr =
  match <|>
  deref
  where
    bool :: Parser s ((Parser.Span -> Text -> Maybe a) -> Expr a)
    bool =
      (\(sp, _) -> \_ -> BTrue $ Known sp) <$> Parser.spanned (Parser.symbol "true") <* spaces <|>
      (\(sp, _) -> \_ -> BFalse $ Known sp) <$> Parser.spanned (Parser.symbol "false") <* spaces

    new :: Parser s ((Parser.Span -> Text -> Maybe a) -> Expr a)
    new =
      (\(sp, e) -> \abstract -> New (Known sp) (e abstract)) <$>
      Parser.spanned
      (Parser.symbol "new" *> Parser.char '[' *>
       expr <* Parser.char ']'
      ) <* spaces

    field :: Parser s Text
    field =
      Parser.takeWhile1 Parser.pDigit <|>
      Parser.takeWhile1 Parser.pLower

    commasep :: forall x. Parser s x -> Parser s [x]
    commasep p = Parser.sepBy p (Parser.char ',' *> spaces)

    args :: Parser s ((Parser.Span -> Text -> Maybe a) -> Vector (Expr a))
    args =
      parens ((\es abstract -> ($ abstract) <$> Vector.fromList es)<$> commasep expr)

    projectOrCall :: Parser s ((Parser.Span -> Text -> Maybe a) -> Expr a)
    projectOrCall =
      (\(sp, (z, as)) ->
         \abstract ->
         foldl (\acc -> either (Project (Known sp) acc) (Call (Known sp) acc . ($ abstract))) (z abstract) as
      ) <$>
      (Parser.spanned $
       (,) <$>
       atom <*>
       many
         (Left <$ Parser.char '.' <*> field <* spaces <|>
          Right <$> args <* spaces
         )
      )

    deref :: Parser s ((Parser.Span -> Text -> Maybe a) -> Expr a)
    deref =
      (\(sp, e) -> \abstract -> Deref (Known sp) (e abstract)) <$> Parser.spanned (Parser.char '*' *> deref) <|>
      projectOrCall

    number :: Parser s ((Parser.Span -> Text -> Maybe a) -> Expr a)
    number =
      (\(sp, n) -> \_ -> Number (Known sp) n) <$>
      (Parser.spanned $
       (negate <$ Parser.char '-' <|> pure id) <*>
       Parser.decimal
      ) <* spaces

    atom :: Parser s ((Parser.Span -> Text -> Maybe a) -> Expr a)
    atom =
      bool <|>
      new <|>
      number <|>
      (\(sp, i) -> \abstract -> maybe (Name (Known sp) i) Var $ abstract sp i) <$> Parser.spanned ident <* spaces <|>
      parens expr <* spaces

    case_ :: Parser s ((Parser.Span -> Text -> Maybe a) -> Case a)
    case_ =
      (\(sp, (c, as)) e ->
         \abstract ->
           Case
             (Known sp)
             c
             as
             (e $ \s n -> B . Index (Known s) <$> Vector.findIndex (n ==) as <|> F <$> abstract s n)
      ) <$>
      Parser.spanned
        ((,) <$>
         ident <*>
         parens (Vector.fromList <$> commasep ident)
        ) <* spaces <* Parser.symbol "=>" <* spaces <*>
      expr

    match :: Parser s ((Parser.Span -> Text -> Maybe a) -> Expr a)
    match =
      (\(sp, (e, bs)) -> \abstract -> Match (Known sp) (e abstract) (($ abstract) <$> bs)) <$>
      (Parser.spanned $
       (,) <$ Parser.symbol "match" <* spaces <*>
       deref <* spaces <*>
       Parser.between
         (Parser.char '{' *> newlines)
         (newlines *> Parser.char '}')
         (Vector.fromList <$> Parser.sepBy case_ (Parser.char ',' <* newlines))
      )

type_ :: forall s a. Parser s ((Parser.Span -> Text -> Maybe a) -> Type a)
type_ = (\(_, e) abstract -> e abstract) <$> self
  where
    self :: Parser s (Parser.Span, (Parser.Span -> Text -> Maybe a) -> Type a)
    self = app

    atom :: Parser s ((Parser.Span -> Text -> Maybe a) -> Type a)
    atom =
      (\(sp, _) -> \_ -> TInt32 $ Known sp) <$> Parser.spanned (Parser.symbol "int32") <* spaces <|>
      (\(sp, _) -> \_ -> TBool $ Known sp) <$> Parser.spanned (Parser.symbol "bool") <* spaces <|>
      (\(sp, _) -> \_ -> TPtr $ Known sp) <$> Parser.spanned (Parser.symbol "ptr") <* spaces <|>
      (\(sp, ts) -> \abstract -> TFun (Known sp) $ fmap ($ abstract) (Vector.fromList ts)) <$>
        Parser.spanned
          (Parser.symbol "fun" *>
          parens (Parser.sepBy type_ (Parser.char ',' <* spaces)) <*
          spaces
          ) <|>
      parens type_ <|>
      (\(sp, i) abstract -> maybe (TName (Known sp) i) TVar $ abstract sp i) <$>
        Parser.spanned ident <* spaces

    app :: Parser s (Parser.Span, (Parser.Span -> Text -> Maybe a) -> Type a)
    app =
      foldl
        (\(spl, l) (spr, r) ->
           let
             sp = spl <> spr
           in
             (sp, \abstract -> TApp (Known sp) (l abstract) (r abstract))
        ) <$>
        Parser.spanned atom <*>
        many (Parser.spanned atom)

datatype :: Parser s ADT
datatype =
  struct <|>
  enum
  where
    struct =
      (\tName tArgs cName cArgs ->
         let
           abstractTy sp v = B . Index (Known sp) <$> Vector.elemIndex v tArgs
         in
           ADT tName tArgs (Ctor cName (($ abstractTy) <$> Vector.fromList cArgs) End)
      ) <$ Parser.symbol "struct" <* Parser.char ' ' <* spaces <*>
      ident <* spaces <*>
      fmap Vector.fromList (many $ ident <* spaces) <* Parser.char '=' <* spaces <*>
      ident <*>
      parens
        (Parser.sepBy
            type_
            (Parser.char ',' <* spaces)
        )

    enum =
      (\tName tArgs cs ->
         let
           abstractTy sp v = B . Index (Known sp) <$> Vector.elemIndex v tArgs
         in
          ADT tName tArgs (cs abstractTy)
      ) <$ Parser.symbol "enum" <* Parser.char ' ' <* spaces <*>
      ident <* spaces <*>
      fmap Vector.fromList (many $ ident <* spaces) <*>
      braces
        ((\cs ->
           \abstractTy ->
             foldr (\(n, as) -> Ctor n (($ abstractTy) <$> Vector.fromList as)) End cs
         ) <$ spaces <*>
         Parser.sepBy
           ((,) <$>
            ident <*>
            parens
              (Parser.sepBy
                type_
                (Parser.char ',' <* spaces)
              ) <*
             spaces
           )
           (Parser.char ',' <* spaces)
        )

function :: Parser s Function
function =
  (\name tArgs args retTy body ->
     let
       args' = ($ abstractTy) <$> args
       abstractTy sp v = B . Index (Known sp) <$> Vector.elemIndex v tArgs
       abstractTm sp v = B . Index (Known sp) <$> Vector.elemIndex v (fst <$> args')
     in
       Function name tArgs args' (retTy abstractTy) (body abstractTm)
  ) <$ Parser.symbol "fn" <* Parser.char ' ' <* spaces <*>
  ident <*>
  (angles
    (Vector.fromList <$>
     Parser.sepBy ident (Parser.char ',' *> spaces)
    ) <|>
   pure mempty
  ) <*>
  parens
    (Vector.fromList <$>
     Parser.sepBy
       ((\i t -> \abstractTy -> (i, t abstractTy)) <$>
        ident <* spaces <* Parser.char ':' <* spaces <*>
        type_
       )
       (Parser.char ',' *> spaces)
    ) <* spaces <* Parser.symbol "->" <* spaces <*>
  type_ <*>
  braces (newlines *> expr <* newlines)

declaration :: Parser s Declaration
declaration =
  DData <$> datatype <|>
  DFunc <$> function

declarations :: Parser s [Declaration]
declarations =
  Parser.sepBy declaration newlines
