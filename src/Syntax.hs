{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language TemplateHaskell #-}
module Syntax where

import Bound (Scope)
import Bound.TH (makeBound)
import Bound.Var (Var)
import Control.Monad (ap)
import Data.Deriving (deriveEq1, deriveOrd1, deriveShow1, deriveEq2, deriveShow2)
import Data.Functor.Classes (Eq1(..), Show1(..), Eq2(..), Show2(..), eq1, compare1, showsPrec1)
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Void (Void)

data WordSize
  = S8
  | S16
  | S32
  | S64
  deriving (Eq, Ord, Show)

data Type a
  = TVar a
  | TApp (Type a) (Type a)
  | TUInt WordSize
  | TInt WordSize
  | TBool
  | TPtr
  | TFun (Vector (Type a))
  | TName Text
  deriving (Functor, Foldable, Traversable)
makeBound ''Type
deriveEq1 ''Type
deriveOrd1 ''Type
deriveShow1 ''Type
instance Eq a => Eq (Type a) where; (==) = eq1
instance Ord a => Ord (Type a) where; compare = compare1
instance Show a => Show (Type a) where; showsPrec = showsPrec1

data Ctors a
  = End
  | Ctor { ctorName :: Text, ctorArgs :: Vector (Type a) }
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Ctors
deriveShow1 ''Ctors
instance Eq a => Eq (Ctors a) where; (==) = eq1
instance Show a => Show (Ctors a) where; showsPrec = showsPrec1

data ADT
  = ADT
  { adtName :: Text
  , adtArgs :: Vector Text
  , adtCtors :: Scope Int Ctors Void
  } deriving Show

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
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Expr
deriveShow1 ''Expr
instance Eq a => Eq (Expr a) where; (==) = eq1
instance Show a => Show (Expr a) where; showsPrec = showsPrec1

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

data FunctionBody ty tm
  = Forall Text (FunctionBody (Var () ty) tm)
  | Arg Text (Type ty) (FunctionBody ty (Var () tm))
  | Done (Type ty) (Expr tm)
  deriving (Functor, Foldable, Traversable)
deriveEq2 ''FunctionBody
deriveShow2 ''FunctionBody
instance Eq ty => Eq1 (FunctionBody ty) where; liftEq = liftEq2 (==)
instance Show ty => Show1 (FunctionBody ty) where; liftShowsPrec = liftShowsPrec2 showsPrec showList
instance (Eq ty, Eq tm) => Eq (FunctionBody ty tm) where; (==) = eq1
instance (Show ty, Show tm) => Show (FunctionBody ty tm) where; showsPrec = showsPrec1

data Function
  = Function
  { funcName :: Text
  , funcBody :: FunctionBody Void Void
  } deriving (Eq, Show)

data Declaration
  = DData ADT
  | DFunc Function
  deriving Show
