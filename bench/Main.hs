{-# language DeriveGeneric #-}
{-# language OverloadedStrings #-}
module Main where

import Control.Applicative ((<|>), optional, some, many)
import Control.DeepSeq (NFData, rnf)
import Control.Monad (replicateM_)
import Criterion.Main
import Data.Foldable (asum, foldl', traverse_)
import Data.IORef (newIORef, readIORef, modifyIORef)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text (readFile)
import Data.Void (Void)
import GHC.Generics (Generic)
import System.Environment (getArgs, withArgs)
import Weigh

import qualified Parser
import qualified Data.Attoparsec.Text as Attoparsec
import qualified Text.Megaparsec as Megaparsec
import qualified Text.Megaparsec.Char as Megaparsec

data Expr = Var Text | Lam Text Expr | App Expr Expr
  deriving (Generic, Show)
instance NFData Expr

{-# noinline parseLambda #-}
parseLambda :: Text -> Either Parser.ParseError Expr
parseLambda = Parser.parse expr
  where
    expr :: Parser.Parser s Expr
    expr =
      lambda <|>
      app

    spaces :: Parser.Parser s ()
    spaces = (Parser.char ' ' *> spaces) <|> pure ()

    ident :: Parser.Parser s Text
    ident = fmap Text.pack (some . asum $ (\c -> c <$ Parser.char c) <$> ['a'..'z']) <* spaces

    lambda :: Parser.Parser s Expr
    lambda =
      Lam <$ Parser.char '\\' <* spaces <*>
      ident <* Parser.char '-' <* Parser.char '>' <* spaces <*>
      expr

    atom :: Parser.Parser s Expr
    atom =
      Var <$> ident <* spaces <|>
      Parser.char '(' *> spaces *> expr <* Parser.char ')' <* spaces

    app :: Parser.Parser s Expr
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

{-# noinline parseLambdaAP #-}
parseLambdaAP :: Text -> Attoparsec.Result Expr
parseLambdaAP = Attoparsec.parse expr
  where
    expr :: Attoparsec.Parser Expr
    expr =
      lambda <|>
      app

    spaces :: Attoparsec.Parser ()
    spaces = (Attoparsec.char ' ' *> spaces) <|> pure ()

    ident :: Attoparsec.Parser Text
    ident = fmap Text.pack (some . asum $ (\c -> c <$ Attoparsec.char c) <$> ['a'..'z']) <* spaces

    lambda :: Attoparsec.Parser Expr
    lambda =
      Lam <$ Attoparsec.char '\\' <* spaces <*>
      ident <* Attoparsec.char '-' <* Attoparsec.char '>' <* spaces <*>
      expr

    atom :: Attoparsec.Parser Expr
    atom =
      Var <$> ident <* spaces <|>
      Attoparsec.char '(' *> spaces *> expr <* Attoparsec.char ')' <* spaces

    app :: Attoparsec.Parser Expr
    app = foldl App <$> atom <*> many atom

manySymbols :: Text -> Either Parser.ParseError Int
manySymbols = Parser.parse (ps <* Parser.eof)
  where
    ps = (+) <$> p <*> (Parser.char ' ' *> ps <|> pure 0)
    p =
      1 <$ Parser.symbol "hello" <|>
      2 <$ Parser.symbol "goopy" <|>
      3 <$ Parser.symbol "wonder" <|>
      4 <$ Parser.symbol "several" <|>
      5 <$ Parser.symbol "plato" <|>
      6 <$ Parser.symbol "ticklish"

manyTextsNaive :: Text -> Either Parser.ParseError Int
manyTextsNaive = Parser.parse (ps <* Parser.eof)
  where
    t :: Text -> Parser.Parser s ()
    t = Text.foldr (\c rest -> Parser.char c *> rest) (pure ())

    ps = (+) <$> p <*> (Parser.char ' ' *> ps <|> pure 0)
    p =
      1 <$ t "hello" <|>
      2 <$ t "goopy" <|>
      3 <$ t "wonder" <|>
      4 <$ t "several" <|>
      5 <$ t "plato" <|>
      6 <$ t "ticklish"

manyTexts :: Text -> Either Parser.ParseError Int
manyTexts = Parser.parse (ps <* Parser.eof)
  where
    ps = (+) <$> p <*> (Parser.char ' ' *> ps <|> pure 0)
    p =
      1 <$ Parser.text "hello" <|>
      2 <$ Parser.text "goopy" <|>
      3 <$ Parser.text "wonder" <|>
      4 <$ Parser.text "several" <|>
      5 <$ Parser.text "plato" <|>
      6 <$ Parser.text "ticklish"

manyTextsMP :: Text -> Either (Megaparsec.ParseErrorBundle Text Void) Int
manyTextsMP = Megaparsec.parse (ps <* Megaparsec.eof) ""
  where
    ps = (+) <$> p <*> (Megaparsec.char ' ' *> ps <|> pure 0)

    p =
      1 <$ Megaparsec.string "hello" <|>
      2 <$ Megaparsec.string "goopy" <|>
      3 <$ Megaparsec.string "wonder" <|>
      4 <$ Megaparsec.string "several" <|>
      5 <$ Megaparsec.string "plato" <|>
      6 <$ Megaparsec.string "ticklish"

manyTextsAP :: Text -> Attoparsec.Result Int
manyTextsAP = Attoparsec.parse (ps <* Attoparsec.endOfInput)
  where
    ps = (+) <$> p <*> (Attoparsec.char ' ' *> ps <|> pure 0)

    p =
      1 <$ Attoparsec.string "hello" <|>
      2 <$ Attoparsec.string "goopy" <|>
      3 <$ Attoparsec.string "wonder" <|>
      4 <$ Attoparsec.string "several" <|>
      5 <$ Attoparsec.string "plato" <|>
      6 <$ Attoparsec.string "ticklish"

main :: IO ()
main = do
  print $ parseLambda "x"
  print $ parseLambda "x y"
  print $ parseLambda "\\x -> y"
  print $ parseLambda "x (\\y -> z)"
  print . parseLambda =<< Text.readFile "bench/res/depth_5.lam"
  benchtype:args <- getArgs
  case benchtype of
    "memory" -> do
      file_5 <- Text.readFile "bench/res/depth_5.lam"
      file_35 <- Text.readFile "bench/res/depth_35.lam"
      mainWith $ do
        func "sage x (\\y -> z)" parseLambda "x (\\y -> z)"
        func "megaparsec x (\\y -> z)" parseLambdaMP "x (\\y -> z)"
        func "attoparsec x (\\y -> z)" parseLambdaAP "x (\\y -> z)"
        func "sage x (\\y -> a b c d e)" parseLambda "x (\\y -> a b c d e)"
        func "megaparsec x (\\y -> a b c d e)" parseLambdaMP "x (\\y -> a b c d e)"
        func "attoparsec x (\\y -> a b c d e)" parseLambdaAP "x (\\y -> a b c d e)"
        func "sage x (\\y -> a b c d ~)" parseLambda "x (\\y -> a b c d ~)"
        func "megaparsec x (\\y -> a b c d ~)" parseLambdaMP "x (\\y -> a b c d ~)"
        func "attoparsec x (\\y -> a b c d ~)" parseLambdaAP "x (\\y -> a b c d ~)"
        wgroup "32B file" $ do
          func' "sage" parseLambda file_5
          func' "megaparsec" parseLambdaMP file_5
          func' "attoparsec" parseLambdaAP file_5
        case args of
          "big":_ ->
            wgroup "37M file" $ do
              func' "sage" parseLambda file_35
              func' "megaparsec" parseLambdaMP file_35
              func' "attoparsec" parseLambdaAP file_35
          _ -> pure ()
    "time" ->
      let (big, args') = case args of; "big":rest -> (True, rest); _ -> (False, args) in
      withArgs args' . defaultMain $
        [ let
            manyGoodInput = "hello goopy wonder several plato ticklish"
            manyBadInput = "hello goopy wonder several plato ticklish boomy"
          in
            bgroup "combinator comparisons"
              [ bench "sage symbols good" $ nf (\input -> let output@Right{} = manySymbols input in output) manyGoodInput
              , bench "sage symbols bad" $ nf (\input -> let output@Left{} = manySymbols input in output) manyBadInput
              , bench "sage texts good" $ nf (\input -> let output@Right{} = manyTexts input in output) manyGoodInput
              , bench "sage texts bad" $ nf (\input -> let output@Left{} = manyTexts input in output) manyBadInput
              , bench "sage texts naive good" $ nf (\input -> let output@Right{} = manyTextsNaive input in output) manyGoodInput
              , bench "sage texts naive bad" $ nf (\input -> let output@Left{} = manyTextsNaive input in output) manyBadInput
              , bench "megaparsec texts good" $ nf (\input -> let output@Right{} = manyTextsMP input in output) manyGoodInput
              , bench "megaparsec texts bad" $ nf (\input -> let output@Left{} = manyTextsMP input in output) manyBadInput
              , bench "attoparsec texts good" $ nf (\input -> let output@Attoparsec.Partial{} = manyTextsAP input in output) manyGoodInput
              , bench "attoparsec texts bad" $ nf (\input -> let output@Attoparsec.Fail{} = manyTextsAP input in output) manyBadInput
              ]
        , bench "sage x (\\y -> z)" $ nf parseLambda "x (\\y -> z)"
        , bench "megaparsec x (\\y -> z)" $ nf parseLambdaMP "x (\\y -> z)"
        , bench "attoparsec x (\\y -> z)" $ nf parseLambdaAP "x (\\y -> z)"
        , bench "sage x (\\y -> a b c d e)" $ nf parseLambda "x (\\y -> a b c d e)"
        , bench "megaparsec x (\\y -> a b c d e)" $ nf parseLambdaMP "x (\\y -> a b c d e)"
        , bench "attoparsec x (\\y -> a b c d e)" $ nf parseLambdaAP "x (\\y -> a b c d e)"
        , bench "sage x (\\y -> a b c d ~)" $ nf parseLambda "x (\\y -> a b c d ~)"
        , bench "megaparsec x (\\y -> a b c d ~)" $ nf parseLambdaMP "x (\\y -> a b c d ~)"
        , bench "attoparsec x (\\y -> a b c d ~)" $ nf parseLambdaAP "x (\\y -> a b c d ~)"
        , env (Text.readFile "bench/res/depth_5.lam") $ \file ->
            bgroup "32B file"
            [ bench "sage" $ nf parseLambda file
            , bench "megaparsec" $ nf parseLambdaMP file
            , bench "attoparsec" $ nf parseLambdaAP file
            ]
        ] <>
        (if big
         then
           [ env (Text.readFile "bench/res/depth_35.lam") $ \file ->
               bgroup "37M file"
               [ bench "sage" $ nf parseLambda file
               , bench "megaparsec" $ nf parseLambdaMP file
               , bench "attoparsec" $ nf parseLambdaAP file
               ]
           ]
         else
           []
        )
