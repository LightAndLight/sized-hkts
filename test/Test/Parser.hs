{-# language OverloadedStrings #-}
{-# language OverloadedLists #-}
module Test.Parser (parserTests) where

import Bound (Var(..))
import Data.Void (Void)
import Test.Hspec

import Syntax (ADT(..), Case(..), Ctors(..), Expr(..), Type(..))
import Parser (parse, eof, datatype, expr, type_)

parserTests :: Spec
parserTests =
  describe "parser" $ do
    describe "expr" $ do
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
    describe "type" $ do
      it "x" $ do
        parse (type_ (const (Nothing :: Maybe Void)) <* eof) "x" `shouldBe` Right (TName "x")
      it "x y z" $ do
        parse (type_ (const (Nothing :: Maybe Void)) <* eof) "x y z" `shouldBe`
          Right (TApp (TApp (TName "x") (TName "y")) (TName "z"))
      it "int32" $ do
        parse (type_ (const (Nothing :: Maybe Void)) <* eof) "int32" `shouldBe` Right TInt32
      it "bool" $ do
        parse (type_ (const (Nothing :: Maybe Void)) <* eof) "bool" `shouldBe` Right TBool
      it "ptr a" $ do
        parse (type_ (const (Nothing :: Maybe Void)) <* eof) "ptr a" `shouldBe` Right (TApp TPtr (TName "a"))
      it "fun(a, bool)" $ do
        parse (type_ (const (Nothing :: Maybe Void)) <* eof) "fun(a, bool)" `shouldBe` Right (TFun [TName "a", TBool])
      it "fun(a, bool) int32" $ do
        parse (type_ (const (Nothing :: Maybe Void)) <* eof) "fun(a, bool) int32" `shouldBe`
          Right (TApp (TFun [TName "a", TBool]) TInt32)
    describe "datatype" $ do
      it "struct Pair a b = Pair(a, b)" $ do
        parse (datatype <* eof) "struct Pair a b = Pair(a, b)" `shouldBe`
          Right (ADT "Pair" ["a", "b"] $ Ctor "Pair" [TVar $ B 0, TVar $ B 1] End)
      it "enum Either a b { Left(a), Right(b) }" $ do
        parse (datatype <* eof) "enum Either a b { Left(a), Right(b) }" `shouldBe`
          Right
          (ADT "Either" ["a", "b"] $
           Ctor "Left" [TVar $ B 0] $
           Ctor "Right" [TVar $ B 1] $
           End
          )
