{-# language OverloadedStrings #-}
{-# language OverloadedLists #-}
module Test.Parser (parserTests) where

import Bound (Var(..))
import Data.Void (Void)
import Test.Hspec
import Text.Sage (Span(..))

import Syntax (ADT(..), Case(..), Ctors(..), Expr(..), Function(..), Index(..), Span(..), Type(..))
import Parser (parse, eof, datatype, expr, function, type_)

parserTests :: Spec
parserTests =
  describe "parser" $ do
    describe "expr" $ do
      it "x" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (expr <* eof) "x" `shouldBe`
          Right (Name (Known $ Span 0 1) "x")
      it "true" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (expr <* eof) "true" `shouldBe`
          Right (BTrue (Known $ Span 0 4))
      it "false" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (expr <* eof) "false" `shouldBe`
          Right (BFalse (Known $ Span 0 5))
      it "1234" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (expr <* eof) "1234" `shouldBe`
          Right (Number (Known $ Span 0 4) 1234)
      it "-1234" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (expr <* eof) "-12345" `shouldBe`
          Right (Number (Known $ Span 0 6) (-12345))
      it "hello" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (expr <* eof) "hello" `shouldBe`
          Right (Name (Known $ Span 0 5) "hello")
      it "f()" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (expr <* eof) "f()" `shouldBe`
          Right (Call (Known $ Span 0 3) (Name (Known $ Span 0 1) "f") [])
      it "f(a, b)" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (expr <* eof) "f(a, b)" `shouldBe`
          Right
            (Call
              (Known $ Span 0 7)
              (Name (Known $ Span 0 1) "f")
              [Name (Known $ Span 2 1) "a", Name (Known $ Span 5 1) "b"]
            )
      it "x.y" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (expr <* eof) "x.y" `shouldBe`
          Right (Project (Known $ Span 0 3) (Name (Known $ Span 0 1) "x") "y")
      it "x.0" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (expr <* eof) "x.0" `shouldBe`
          Right (Project (Known $ Span 0 3) (Name (Known $ Span 0 1) "x") "0")
      it "*x" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (expr <* eof) "*x" `shouldBe`
          Right (Deref (Known $ Span 0 2) (Name (Known $ Span 1 1) "x"))
      it "**x" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (expr <* eof) "**x" `shouldBe`
          Right (Deref (Known $ Span 0 3) $ Deref (Known $ Span 1 2) $ Name (Known $ Span 2 1) "x")
      it "new[0]" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (expr <* eof) "new[0]" `shouldBe`
          Right (New (Known $ Span 0 6) (Number (Known $ Span 4 1) 0))
      it "*new[0]" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (expr <* eof) "*new[0]" `shouldBe`
          Right (Deref (Known $ Span 0 7) $ New (Known $ Span 1 6) (Number (Known $ Span 5 1) 0))
      it "match x { Left(e) => e(1), Right(a) => 1 }" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (expr <* eof) "match x { Left(e) => e(1), Right(a) => 1 }" `shouldBe`
          Right
            (Match (Known $ Span 0 42)
              (Name (Known $ Span 6 1) "x")
              [ Case (Known $ Span 10 7) "Left" ["e"] $
                Call (Known $ Span 21 4) (Var . B $ Index (Known $ Span 21 1) 0) [Number (Known $ Span 23 1) 1]
              , Case (Known $ Span 27 8) "Right" ["a"] $
                Number (Known $ Span 39 1) 1
              ]
            )
    describe "type" $ do
      it "x" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (type_ <* eof) "x" `shouldBe`
          Right (TName (Known $ Span 0 1) "x")
      it "x y z" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (type_ <* eof) "x y z" `shouldBe`
          Right
          (TApp
            (Known $ Span 0 5)
            (TApp
              (Known $ Span 0 3)
              (TName (Known $ Span 0 1) "x")
              (TName (Known $ Span 2 1) "y"))
            (TName (Known $ Span 4 1) "z")
          )
      it "int32" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (type_ <* eof) "int32" `shouldBe`
          Right (TInt32 (Known $ Span 0 5))
      it "bool" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (type_ <* eof) "bool" `shouldBe`
          Right (TBool (Known $ Span 0 4))
      it "ptr a" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (type_ <* eof) "ptr a" `shouldBe`
          Right (TApp (Known $ Span 0 5) (TPtr (Known $ Span 0 3)) (TName (Known $ Span 4 1) "a"))
      it "fun(a, bool)" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (type_ <* eof) "fun(a, bool)" `shouldBe`
          Right (TFun (Known $ Span 0 12) [TName (Known $ Span 4 1) "a", TBool (Known $ Span 7 4)])
      it "fun(a, bool) int32" $ do
        (\e -> e (\_ _ -> Nothing :: Maybe Void)) <$> parse (type_ <* eof) "fun(a, bool) int32" `shouldBe`
          Right
          (TApp (Known $ Span 0 18)
            (TFun (Known $ Span 0 12) [TName (Known $ Span 4 1) "a", TBool (Known $ Span 7 4)])
            (TInt32 (Known $ Span 13 5))
          )
    describe "datatype" $ do
      it "struct Pair a b = Pair(a, b)" $ do
        parse (datatype <* eof) "struct Pair a b = Pair(a, b)" `shouldBe`
          Right
            (ADT "Pair" ["a", "b"] $
             Ctor "Pair" [TVar . B $ Index (Known $ Span 23 1) 0, TVar . B $ Index (Known $ Span 26 1) 1] End
            )
      it "enum Either a b { Left(a), Right(b) }" $ do
        parse (datatype <* eof) "enum Either a b { Left(a), Right(b) }" `shouldBe`
          Right
          (ADT "Either" ["a", "b"] $
           Ctor "Left" [TVar . B $ Index (Known $ Span 23 1) 0] $
           Ctor "Right" [TVar . B $ Index (Known $ Span 33 1) 1] $
           End
          )
    describe "function" $ do
      it "fn const<a,b>(x: a, y: b) -> a {\n  x\n}" $ do
        parse (function <* eof) "fn const<a,b>(x: a, y: b) -> a {\n  x\n}" `shouldBe`
          Right
            (Function
               "const"
               ["a", "b"]
               [ ("x", TVar . B $ Index (Known $ Span 17 1) 0)
               , ("y", TVar . B $ Index (Known $ Span 23 1) 1)
               ]
               (TVar . B $ Index (Known $ Span 29 1) 0)
               (Var . B $ Index (Known $ Span 35 1) 0)
            )
