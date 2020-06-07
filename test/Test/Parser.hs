{-# language OverloadedStrings #-}
module Test.Parser (parserTests) where

import Control.Applicative ((<|>), some)
import Test.Hspec
import qualified Data.Set as Set

import Parser (Label(..), ParseError(..), (<?>), parse, char)

parserTests :: Spec
parserTests =
  describe "parser" $ do
    it "parse (char 'a') \"a\"" $ do
      let
        input = "a"
        output = Right ()
      parse (char 'a') input `shouldBe` output
    it "parse (char 'a') \"b\"" $ do
      let
        input = "b"
        output = Left (Unexpected 0 (Set.fromList [Char 'a']) False)
      parse (char 'a') input `shouldBe` output
    it "parse (char 'a' *> char 'b') \"ab\"" $ do
      let
        input = "ab"
        output = Right ()
      parse (char 'a' *> char 'b') input `shouldBe` output
    it "parse (char 'a' *> char 'b') \"ac\"" $ do
      let
        input = "ac"
        output = Left (Unexpected 1 (Set.fromList [Char 'b']) False)
      parse (char 'a' *> char 'b') input `shouldBe` output
    it "parse (char 'a' <|> char 'b') \"a\"" $ do
      let
        input = "a"
        output = Right ()
      parse (char 'a' <|> char 'b') input `shouldBe` output
    it "parse (char 'a' <|> char 'b') \"b\"" $ do
      let
        input = "b"
        output = Right ()
      parse (char 'a' <|> char 'b') input `shouldBe` output
    it "parse (char 'a' <|> char 'b') \"c\"" $ do
      let
        input = "c"
        output = Left (Unexpected 0 (Set.fromList [Char 'a', Char 'b']) False)
      parse (char 'a' <|> char 'b') input `shouldBe` output
    it "parse (char 'a' *> char 'x' <|> char 'b' *> char 'y' <|> char 'c' *> char 'z') \"d\"" $ do
      let
        input = "d"
        output = Left (Unexpected 0 (Set.fromList [Char 'a', Char 'b', Char 'c']) False)
      parse (char 'a' *> char 'x' <|> char 'b' *> char 'y' <|> char 'c' *> char 'z') input `shouldBe` output
    it "parse (char 'a' *> char 'x' <|> char 'b' *> char 'y' <|> char 'c' *> char 'z') \"bz\"" $ do
      let
        input = "bz"
        output = Left (Unexpected 1 (Set.fromList [Char 'y']) False)
      parse (char 'a' *> char 'x' <|> char 'b' *> char 'y' <|> char 'c' *> char 'z') input `shouldBe` output
    it "parse (char 'a' *> char 'x' <|> char 'b' *> char 'y' <|> char 'c' *> char 'z') \"c\"" $ do
      let
        input = "c"
        output = Left (Unexpected 1 (Set.fromList [Char 'z']) False)
      parse (char 'a' *> char 'x' <|> char 'b' *> char 'y' <|> char 'c' *> char 'z') input `shouldBe` output
    it "parse (char 'a' *> char 'x' <?> \"ax\" <|> char 'b' *> char 'y' <?> \"by\" <|> char 'c' *> char 'z' <?> \"cz\") \"d\"" $ do
      let
        input = "d"
        output = Left (Unexpected 0 (Set.fromList [Named "ax", Named "by", Named "cz"]) False)
      parse
        (char 'a' *> char 'x' <?> "ax" <|> char 'b' *> char 'y' <?> "by" <|> char 'c' *> char 'z' <?> "cz")
        input
        `shouldBe`
        output
    it "parse (char '(' *> some (char 'x') <* char ')') \"(xx)\"" $ do
      let
        input = "(xx)"
        output = Right [(), ()]
      parse (char '(' *> some (char 'x') <* char ')') input `shouldBe` output
    it "parse (char '(' *> some (char 'x') <* char ')') \"(xxy\"" $ do
      let
        input = "(xxy"
        output = Left (Unexpected 3 (Set.fromList [Char ')', Char 'x']) False)
      parse (char '(' *> some (char 'x') <* char ')') input `shouldBe` output
