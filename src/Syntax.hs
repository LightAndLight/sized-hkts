{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Syntax where

import Bound.TH (makeBound)
import Bound.Var (Var(..), unvar)
import Control.Lens.Getter ((^.))
import Control.Lens.Lens (Lens', lens)
import Control.Lens.Setter ((.~))
import Control.Monad (ap)
import Control.Monad.Except (ExceptT(..), runExceptT)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Foldable (fold)
import Data.Function ((&))
import Data.Functor.Classes (Eq1(..), eq1, showsPrec1)
import qualified Data.List as List
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Vector (Vector)
import Data.Void (Void, absurd)
import qualified Text.Sage as Sage

data Span = Unknown | Known Sage.Span
  deriving (Eq, Ord, Show)

instance Semigroup Span where
  Unknown <> a = a
  a <> Unknown = a
  Known a <> Known b = Known (a <> b)

data Type a
  = TVar a
  | TApp !Span (Type a) (Type a)
  | TInt32 !Span
  | TBool !Span
  | TPtr !Span
  | TFun !Span (Vector (Type a))
  | TName !Span Text
  deriving (Functor, Foldable, Traversable)
makeBound ''Type
-- deriveEq1 ''Type
-- instance Eq a => Eq (Type a) where; (==) = eq1
-- deriving instance Ord a => Ord (Type a)
deriveShow1 ''Type
instance Eq1 Type where
  liftEq f (TVar a) (TVar a') = f a a'
  liftEq f (TApp _ a b) (TApp _ a' b') = liftEq f a a' && liftEq f b b'
  liftEq _ (TInt32 _) (TInt32 _) = True
  liftEq _ (TBool _) (TBool _) = True
  liftEq _ (TPtr _) (TPtr _) = True
  liftEq f (TFun _ ts) (TFun _ ts') = liftEq (liftEq f) ts ts'
  liftEq _ (TName _ a) (TName _ a') = a == a'
  liftEq _ _ _ = False
instance Eq a => Eq (Type a) where (==) = eq1
instance Ord a => Ord (Type a) where
  compare (TVar a) (TVar a') = compare a a'
  compare TVar{} _ = LT
  compare _ TVar{} = GT

  compare (TApp _ a b) (TApp _ a' b') =
    case compare a a' of
      EQ -> compare b b'
      c -> c
  compare TApp{} _ = LT
  compare _ TApp{} = GT

  compare (TInt32 _) (TInt32 _) = EQ
  compare TInt32{} _ = LT
  compare _ TInt32{} = GT

  compare (TBool _) (TBool _) = EQ
  compare TBool{} _ = LT
  compare _ TBool{} = GT

  compare (TPtr _) (TPtr _) = EQ
  compare TPtr{} _ = LT
  compare _ TPtr{} = GT

  compare (TFun _ a) (TFun _ a') = compare a a'
  compare TFun{} _ = LT
  compare _ TFun{} = GT

  compare (TName _ a) (TName _ a') = compare a a'
  -- compare TName{} _ = LT
  -- compare _ TName{} = GT
instance Show a => Show (Type a) where; showsPrec = showsPrec1

typeSpan :: forall a. Lens' a Span -> Lens' (Type a) Span
typeSpan as = lens get set
  where
    get :: Type a -> Span
    get t =
      case t of
        TVar a -> a ^. as
        TApp sp _ _ -> sp
        TInt32 sp -> sp
        TBool sp -> sp
        TPtr sp -> sp
        TFun sp _ -> sp
        TName sp _ -> sp

    set :: Type a -> Span -> Type a
    set t sp' =
      case t of
        TVar a -> TVar (a & as .~ sp')
        TApp _ a b -> TApp sp' a b
        TInt32 _ -> TInt32 sp'
        TBool _ -> TBool sp'
        TPtr _ -> TPtr sp'
        TFun _ a -> TFun sp' a
        TName _ a -> TName sp' a

unApply :: Type a -> (Type a, [Type a])
unApply = go []
  where
    go ts t =
      case t of
        TApp _ a b -> go (b:ts) a
        _ -> (t, ts)

data TMeta = TMeta !Span {-# UNPACK #-} !Int
  deriving Show
instance Eq TMeta where; TMeta _ v == TMeta _ v' = v == v'
instance Ord TMeta where; TMeta _ v `compare` TMeta _ v' = v `compare` v'

prettyTMeta :: TMeta -> Text
prettyTMeta (TMeta _ n) = Text.pack $ '?' : show n

tmetaSpan :: TMeta -> Span
tmetaSpan (TMeta s _) = s

type TypeM = ExceptT TMeta Type

eitherTMetaSpan :: forall a. Lens' a Span -> Lens' (Either TMeta a) Span
eitherTMetaSpan as = lens get set
  where
    get :: Either TMeta a -> Span
    get t =
      case t of
        Left (TMeta sp _) -> sp
        Right a -> a ^. as

    set :: Either TMeta a -> Span -> Either TMeta a
    set t sp' =
      case t of
        Left (TMeta _ v) -> Left (TMeta sp' v)
        Right a -> Right (a & as .~ sp')

typemSpan :: forall a. Lens' a Span -> Lens' (TypeM a) Span
typemSpan as = lens get set
  where
    get :: TypeM a -> Span
    get t = unTypeM t ^. typeSpan (eitherTMetaSpan as)

    set :: TypeM a -> Span -> TypeM a
    set t sp' = TypeM $ unTypeM t & typeSpan (eitherTMetaSpan as) .~ sp'

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
    TApp _ a b ->
      prettyType var a <>
      " " <>
      (case b of
         TApp{} -> parens
         _ -> id
      ) (prettyType var b)
    TInt32 _ -> "int32"
    TBool _ -> "bool"
    TPtr _ -> "ptr"
    TFun _ args ->
      "fun(" <>
      fold
        (List.intersperse ", " $
         foldr ((:) . prettyType var) [] args
        ) <>
      ")"
    TName _ n -> n

data Ctors a
  = End
  | Ctor { ctorName :: Text, ctorArgs :: Vector (Type a), ctorRest :: Ctors a }
  deriving (Functor, Foldable, Traversable)
-- deriveEq1 ''Ctors
-- instance Eq a => Eq (Ctors a) where; (==) = eq1
deriving instance Eq a => Eq (Ctors a)
deriveShow1 ''Ctors
instance Show a => Show (Ctors a) where; showsPrec = showsPrec1

ctorsToList :: Ctors a -> [(Text, Vector (Type a))]
ctorsToList cs =
  case cs of
    End -> []
    Ctor a b c -> (a, b) : ctorsToList c

data Index
  = Index !Span {-# UNPACK #-} !Int
  deriving Show

voidSpan :: Lens' Void Span
voidSpan = lens absurd absurd

indexSpan :: Lens' Index Span
indexSpan = lens get set
  where
    get (Index sp _) = sp
    set (Index _ i) sp' = Index sp' i

varSpan :: Lens' a Span -> Lens' b Span -> Lens' (Var a b) Span
varSpan as bs = lens get set
  where
    get = unvar (^. as) (^. bs)
    set = unvar (\a new -> B $ a & as .~ new) (\b new -> F $ b & bs .~ new)

instance Eq Index where; Index _ i == Index _ i' = i == i'
instance Ord Index where; Index _ i `compare` Index _ i' = i `compare` i'

getIndex :: Index -> Int
getIndex (Index _ i) = i

data ADT
  = ADT
  { adtName :: Text
  , adtArgs :: Vector Text
  , adtCtors :: Ctors (Var Index Void)
  } deriving (Eq, Show)

data Case a
  = Case
  { caseCtorSpan :: !Span
  , caseCtor :: Text
  , caseArgs :: Vector Text
  , caseExpr :: Expr (Var Index a)
  } deriving (Functor, Foldable, Traversable)

data Expr a
  = Var a
  | Name !Span Text

  | Let (Vector (Text, Expr a)) (Expr a)
  | Call !Span (Expr a) (Vector (Expr a))

  | Number !Span Integer

  | BTrue !Span
  | BFalse !Span

  | New !Span (Expr a)
  | Deref !Span (Expr a)

  | Project !Span (Expr a) Text
  | Match !Span (Expr a) (Vector (Case a))
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
bindExpr_Case f (Case sp name args e) = Case sp name args (e >>= unvar (Var . B) (fmap F . f))

instance Applicative Expr where; pure = Var; (<*>) = ap
instance Monad Expr where
  expr >>= f =
    case expr of
      Var a -> f a
      Name sp n -> Name sp n
      Let es b -> Let ((\(n, e) -> (n, e >>= f)) <$> es) (b >>= f)
      Call sp a args -> Call sp (a >>= f) ((>>= f) <$> args)
      Number sp n -> Number sp n
      BTrue sp -> BTrue sp
      BFalse sp -> BFalse sp
      New sp v -> New sp (v >>= f)
      Deref sp p -> Deref sp (p >>= f)
      Project sp a field -> Project sp (a >>= f) field
      Match sp e cs -> Match sp (e >>= f) (bindExpr_Case f <$> cs)

data Function
  = Function
  { funcName :: Text
  , funcTyArgs :: Vector Text
  , funcArgs :: Vector (Text, Type (Var Index Void)) -- indices from funcTyArgs
  , funcRetTy :: Type (Var Index Void) -- indices from funcTyArgs
  , funcBody :: Expr (Var Index Void) -- indices from funcArgs
  } deriving (Eq, Show)

data Declaration
  = DData ADT
  | DFunc Function
  deriving Show
