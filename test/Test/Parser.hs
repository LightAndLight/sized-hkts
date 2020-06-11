{-# language OverloadedStrings #-}
{-# language OverloadedLists #-}
module Test.Parser (parserTests) where

import Test.Hspec

import Syntax (Expr(..))
import Parser (parse, eof, expr)

parserTests :: Spec
parserTests =
  describe "parser" $ do
    it "true" $ do
      parse (expr <* eof) "true" `shouldBe` Right BTrue
    it "false" $ do
      parse (expr <* eof) "false" `shouldBe` Right BFalse
    it "1234" $ do
      parse (expr <* eof) "1234" `shouldBe` Right (Number 1234)
    it "-1234" $ do
      parse (expr <* eof) "-12345" `shouldBe` Right (Number (-12345))
    it "hello" $ do
      parse (expr <* eof) "hello" `shouldBe` Right (Name "hello")
    it "f()" $ do
      parse (expr <* eof) "f()" `shouldBe` Right (Call (Name "f") [])
    it "f(a, b)" $ do
      parse (expr <* eof) "f(a, b)" `shouldBe` Right (Call (Name "f") [Name "a", Name "b"])
    it "x.y" $ do
      parse (expr <* eof) "x.y" `shouldBe` Right (Project (Name "x") "y")
    it "x.0" $ do
      parse (expr <* eof) "x.0" `shouldBe` Right (Project (Name "x") "0")
    it "*x" $ do
      parse (expr <* eof) "*x" `shouldBe` Right (Deref (Name "x"))
    it "**x" $ do
      parse (expr <* eof) "**x" `shouldBe` Right (Deref $ Deref $ Name "x")
    it "new[0]" $ do
      parse (expr <* eof) "new[0]" `shouldBe` Right (New (Number 0))
    it "*new[0]" $ do
      parse (expr <* eof) "*new[0]" `shouldBe` Right (Deref $ New (Number 0))
