{-# language DeriveGeneric #-}
{-# language OverloadedStrings #-}
module Main where

import Control.Applicative ((<|>), optional, some, many)
import Control.DeepSeq (NFData, rnf)
import Control.Monad (replicateM_)
import Criterion.Main
import Data.Foldable (asum)
import Data.IORef (newIORef, readIORef, modifyIORef)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Void (Void)
import GHC.Generics (Generic)

import qualified Parser
import qualified Text.Megaparsec as Megaparsec
import qualified Text.Megaparsec.Char as Megaparsec

data Expr = Var Text | Lam Text Expr | App Expr Expr
  deriving (Generic, Show)
instance NFData Expr

{-# noinline parseLambda #-}
parseLambda :: Text -> Either Parser.ParseError Expr
parseLambda = Parser.parse expr
  where
    expr :: Parser.Parser Expr
    expr =
      lambda <|>
      app

    spaces :: Parser.Parser ()
    spaces = (Parser.char ' ' *> spaces) <|> pure ()

    ident :: Parser.Parser Text
    ident = fmap Text.pack (some . asum $ (\c -> c <$ Parser.char c) <$> ['a'..'z']) <* spaces

    lambda :: Parser.Parser Expr
    lambda =
      Lam <$ Parser.char '\\' <* spaces <*>
      ident <* Parser.char '-' <* Parser.char '>' <* spaces <*>
      expr

    atom :: Parser.Parser Expr
    atom =
      Var <$> ident <* spaces <|>
      Parser.char '(' *> spaces *> expr <* Parser.char ')' <* spaces

    app :: Parser.Parser Expr
    app = foldl App <$> atom <*> many atom

{-# noinline parseLambdaMP #-}
parseLambdaMP :: Text -> Either (Megaparsec.ParseErrorBundle Text Void) Expr
parseLambdaMP = Megaparsec.parse expr ""
  where
    expr :: Megaparsec.Parsec Void Text Expr
    expr =
      lambda <|>
      app

    spaces :: Megaparsec.Parsec Void Text ()
    spaces = (Megaparsec.char ' ' *> spaces) <|> pure ()

    ident :: Megaparsec.Parsec Void Text Text
    ident = fmap Text.pack (some . asum $ (\c -> c <$ Megaparsec.char c) <$> ['a'..'z']) <* spaces

    lambda :: Megaparsec.Parsec Void Text Expr
    lambda =
      Lam <$ Megaparsec.char '\\' <* spaces <*>
      ident <* Megaparsec.char '-' <* Megaparsec.char '>' <* spaces <*>
      expr

    atom :: Megaparsec.Parsec Void Text Expr
    atom =
      Var <$> ident <* spaces <|>
      Megaparsec.char '(' *> spaces *> expr <* Megaparsec.char ')' <* spaces

    app :: Megaparsec.Parsec Void Text Expr
    app = foldl App <$> atom <*> many atom

main :: IO ()
main = do
  print $ parseLambda "x"
  print $ parseLambda "x y"
  print $ parseLambda "\\x -> y"
  print $ parseLambda "x (\\y -> z)"
    {-
  count <- newIORef 0
  replicateM_ 10000000 $ do
    let
      a = parseLambdaMP "x (\\y -> z)"
      () = rnf a
    modifyIORef count (+1)
  print =<< readIORef count
-}
  defaultMain
    [ bench "sage x (\\y -> z)" $ nf parseLambda "x (\\y -> z)"
    , bench "megaparsec x (\\y -> z)" $ nf parseLambdaMP "x (\\y -> z)"
    ]
