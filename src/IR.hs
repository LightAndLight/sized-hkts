{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language TemplateHaskell #-}
module IR where

import Bound.Var (Var(..), unvar)
import Data.Deriving (deriveEq1, deriveOrd1, deriveShow1, deriveEq2, deriveShow2)
import Data.Functor.Classes (Eq1(..), Show1(..), Eq2(..), Show2(..), eq1, compare1, showsPrec1)
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Void (Void)
import Data.Word (Word8, Word16, Word32, Word64)
import Data.Int (Int8, Int16, Int32, Int64)

import Syntax (Type)

data Expr ty tm
  = Var tm
  | Name Text

  | Let (Vector (Text, Expr ty tm)) (Expr ty tm)
  | Inst Text (Vector (Type ty))
  | Call (Expr ty tm) (Vector (Expr ty tm))

  | UInt8 Word8
  | UInt16 Word16
  | UInt32 Word32
  | UInt64 Word64

  | Int8 Int8
  | Int16 Int16
  | Int32 Int32
  | Int64 Int64

  | BTrue
  | BFalse

  | New (Expr ty tm)
  | Deref (Expr ty tm)
  deriving (Functor, Foldable, Traversable)
deriveEq2 ''Expr
deriveShow2 ''Expr
instance (Eq ty) => Eq1 (Expr ty) where; liftEq = liftEq2 (==)
instance (Show ty) => Show1 (Expr ty) where; liftShowsPrec = liftShowsPrec2 showsPrec showList
instance (Eq ty, Eq tm) => Eq (Expr ty tm) where; (==) = eq1
instance (Show ty, Show tm) => Show (Expr ty tm) where; showsPrec = showsPrec1

newtype KMeta = KMeta Int
  deriving (Eq, Ord, Show)

data Kind = KType | KArr Kind Kind | KVar KMeta
  deriving (Eq, Ord, Show)

data Constraint a
  = CSized (Type a)
  | CForall Text Kind (Constraint (Var () a))
  | CImplies (Constraint a) (Constraint a)
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Constraint
deriveOrd1 ''Constraint
deriveShow1 ''Constraint
instance Eq a => Eq (Constraint a) where; (==) = eq1
instance Ord a => Ord (Constraint a) where; compare = compare1
instance Show a => Show (Constraint a) where; showsPrec = showsPrec1

bindConstraint :: (a -> Type b) -> Constraint a -> Constraint b
bindConstraint f c =
  case c of
    CSized t -> CSized (t >>= f)
    CImplies a b -> CImplies (f `bindConstraint` a) (f `bindConstraint` b)
    CForall n k a -> CForall n k (unvar (pure . B) (fmap F . f) `bindConstraint` a)

data FunctionBody ty tm
  = Forall Text Kind (FunctionBody (Var () ty) tm)
  | Arg Text (Type ty) (FunctionBody ty (Var () tm))
  | Constraint (Constraint ty) (FunctionBody ty tm)
  | Done (Type ty) (Expr ty tm)
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

data TypeScheme ty
  = SForall Text Kind (TypeScheme (Var () ty))
  | SDone (Vector (Constraint ty)) (Vector (Type ty)) (Type ty)
deriveEq1 ''TypeScheme
deriveShow1 ''TypeScheme
instance Eq ty => Eq (TypeScheme ty) where; (==) = eq1
instance Show ty => Show (TypeScheme ty) where; showsPrec = showsPrec1
