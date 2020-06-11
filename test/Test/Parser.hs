{-# language OverloadedStrings #-}
{-# language OverloadedLists #-}
module Test.Parser (parserTests) where

import Bound (Var(..))
import Data.Void (Void)
import Test.Hspec

import Syntax (Case(..), Expr(..))
import Parser (parse, eof, expr)

parserTests :: Spec
parserTests =
  describe "parser" $ do
    it "true" $ do
      parse (expr (const (Nothing :: Maybe Void)) <* eof) "true" `shouldBe` Right BTrue
    it "false" $ do
      parse (expr (const (Nothing :: Maybe Void)) <* eof) "false" `shouldBe` Right BFalse
    it "1234" $ do
      parse (expr (const (Nothing :: Maybe Void)) <* eof) "1234" `shouldBe` Right (Number 1234)
    it "-1234" $ do
      parse (expr (const (Nothing :: Maybe Void)) <* eof) "-12345" `shouldBe` Right (Number (-12345))
    it "hello" $ do
      parse (expr (const (Nothing :: Maybe Void)) <* eof) "hello" `shouldBe` Right (Name "hello")
    it "f()" $ do
      parse (expr (const (Nothing :: Maybe Void)) <* eof) "f()" `shouldBe` Right (Call (Name "f") [])
    it "f(a, b)" $ do
      parse (expr (const (Nothing :: Maybe Void)) <* eof) "f(a, b)" `shouldBe` Right (Call (Name "f") [Name "a", Name "b"])
    it "x.y" $ do
      parse (expr (const (Nothing :: Maybe Void)) <* eof) "x.y" `shouldBe` Right (Project (Name "x") "y")
    it "x.0" $ do
      parse (expr (const (Nothing :: Maybe Void)) <* eof) "x.0" `shouldBe` Right (Project (Name "x") "0")
    it "*x" $ do
      parse (expr (const (Nothing :: Maybe Void)) <* eof) "*x" `shouldBe` Right (Deref (Name "x"))
    it "**x" $ do
      parse (expr (const (Nothing :: Maybe Void)) <* eof) "**x" `shouldBe` Right (Deref $ Deref $ Name "x")
    it "new[0]" $ do
      parse (expr (const (Nothing :: Maybe Void)) <* eof) "new[0]" `shouldBe` Right (New (Number 0))
    it "*new[0]" $ do
      parse (expr (const (Nothing :: Maybe Void)) <* eof) "*new[0]" `shouldBe` Right (Deref $ New (Number 0))
    it "match x { Left(e) => e(1), Right(a) => 1 }" $ do
      parse (expr (const (Nothing :: Maybe Void)) <* eof) "match x { Left(e) => e(1), Right(a) => 1 }" `shouldBe`
        Right
          (Match
            (Name "x")
            [ Case "Left" ["e"] (Call (Var $ B 0) [Number 1])
            , Case "Right" ["a"] (Number 1)
            ]
          )
