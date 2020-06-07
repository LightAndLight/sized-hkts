{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Syntax where

import Bound.TH (makeBound)
import Bound.Var (Var(..), unvar)
import Control.Monad (ap)
import Control.Monad.Except (ExceptT(..), runExceptT)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Foldable (fold)
import Data.Functor.Classes (eq1, showsPrec1)
import qualified Data.List as List
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Void (Void)

data Type a
  = TVar a
  | TApp (Type a) (Type a)
  | TInt32
  | TBool
  | TPtr
  | TFun (Vector (Type a))
  | TName Text
  deriving (Functor, Foldable, Traversable)
makeBound ''Type
deriveEq1 ''Type
deriveShow1 ''Type
instance Eq a => Eq (Type a) where; (==) = eq1
deriving instance Ord a => Ord (Type a)
instance Show a => Show (Type a) where; showsPrec = showsPrec1

unApply :: Type a -> (Type a, [Type a])
unApply = go []
  where
    go ts t =
      case t of
        TApp a b -> go (b:ts) a
        _ -> (t, ts)

newtype TMeta = TMeta Int
  deriving (Eq, Ord, Show)

type TypeM = ExceptT TMeta Type

pattern TypeM :: Type (Either TMeta ty) -> TypeM ty
pattern TypeM a = ExceptT a

unTypeM :: TypeM ty -> Type (Either TMeta ty)
unTypeM = runExceptT


parens :: Text -> Text
parens a = "(" <> a <> ")"

prettyType :: (a -> Text) -> Type a -> Text
prettyType var ty =
  case ty of
    TVar a -> var a
    TApp a b ->
      prettyType var a <>
      " " <>
      (case b of
         TApp{} -> parens
         _ -> id
      ) (prettyType var b)
    TInt32 -> "int32"
    TBool -> "bool"
    TPtr -> "ptr"
    TFun args ->
      "fun(" <>
      fold
        (List.intersperse ", " $
         foldr ((:) . prettyType var) [] args
        ) <>
      ")"
    TName n -> n

data Ctors a
  = End
  | Ctor { ctorName :: Text, ctorArgs :: Vector (Type a), ctorRest :: Ctors a }
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Ctors
deriveShow1 ''Ctors
instance Eq a => Eq (Ctors a) where; (==) = eq1
instance Show a => Show (Ctors a) where; showsPrec = showsPrec1

ctorsToList :: Ctors a -> [(Text, Vector (Type a))]
ctorsToList cs =
  case cs of
    End -> []
    Ctor a b c -> (a, b) : ctorsToList c

data ADT
  = ADT
  { adtName :: Text
  , adtArgs :: Vector Text
  , adtCtors :: Ctors (Var Int Void)
  } deriving Show

data Case a
  = Case
  { caseCtor :: Text
  , caseArgs :: Vector Text
  , caseExpr :: Expr (Var Int a)
  } deriving (Functor, Foldable, Traversable)

data Expr a
  = Var a
  | Name Text

  | Let (Vector (Text, Expr a)) (Expr a)
  | Call (Expr a) (Vector (Expr a))

  | Number Integer

  | BTrue
  | BFalse

  | New (Expr a)
  | Deref (Expr a)

  | Project (Expr a) Text
  | Match (Expr a) (Vector (Case a))
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Case
deriveShow1 ''Case
instance Eq a => Eq (Case a) where; (==) = eq1
instance Show a => Show (Case a) where; showsPrec = showsPrec1

deriveEq1 ''Expr
deriveShow1 ''Expr
instance Eq a => Eq (Expr a) where; (==) = eq1
instance Show a => Show (Expr a) where; showsPrec = showsPrec1

bindExpr_Case :: (a -> Expr b) -> Case a -> Case b
bindExpr_Case f (Case name args e) = Case name args (e >>= unvar (Var . B) (fmap F . f))

instance Applicative Expr where; pure = Var; (<*>) = ap
instance Monad Expr where
  expr >>= f =
    case expr of
      Var a -> f a
      Name n -> Name n
      Let es b -> Let ((\(n, e) -> (n, e >>= f)) <$> es) (b >>= f)
      Call a args -> Call (a >>= f) ((>>= f) <$> args)
      Number n -> Number n
      BTrue -> BTrue
      BFalse -> BFalse
      New v -> New (v >>= f)
      Deref p -> Deref (p >>= f)
      Project a field -> Project (a >>= f) field
      Match e cs -> Match (e >>= f) (bindExpr_Case f <$> cs)

data Function
  = Function
  { funcName :: Text
  , funcTyArgs :: Vector Text
  , funcArgs :: Vector (Text, Type (Var Int Void)) -- indices from funcTyArgs
  , funcRetTy :: Type (Var Int Void) -- indices from funcTyArgs
  , funcBody :: Expr (Var Int Void) -- indices from funcArgs
  } deriving (Eq, Show)

data Declaration
  = DData ADT
  | DFunc Function
  deriving Show
