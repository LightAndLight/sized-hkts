{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language OverloadedLists #-}
{-# language TemplateHaskell #-}
{-# language TypeApplications #-}
module IR where

import Bound.Var (Var(..), unvar)
import Control.Lens.Setter (over, mapped)
import Control.Lens.Tuple (_1)
import Data.Bifunctor (bimap)
import Data.Deriving (deriveEq1, deriveOrd1, deriveShow1, deriveEq2, deriveShow2)
import Data.Functor.Classes (Eq1(..), Show1(..), Eq2(..), Show2(..), eq1, compare1, showsPrec1)
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Void (Void)
import Data.Word (Word8, Word16, Word32, Word64)
import Data.Int (Int8, Int16, Int32, Int64)

import Syntax (Type(..))

data Expr ty tm
  = Var tm
  | Name Text

  | Let (Vector ((Text, Expr ty tm), Type ty)) (Expr ty tm)
  | Inst Text (Vector (Type ty))
  | Ctor Text (Vector (Type ty))
  | Call (Expr ty tm) (Vector (Expr ty tm)) (Type ty)

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

  | New (Expr ty tm) (Type ty)
  | Deref (Expr ty tm)
  deriving (Functor, Foldable, Traversable)
deriveEq2 ''Expr
deriveShow2 ''Expr
instance (Eq ty) => Eq1 (Expr ty) where; liftEq = liftEq2 (==)
instance (Show ty) => Show1 (Expr ty) where; liftShowsPrec = liftShowsPrec2 showsPrec showList
instance (Eq ty, Eq tm) => Eq (Expr ty tm) where; (==) = eq1
instance (Show ty, Show tm) => Show (Expr ty tm) where; showsPrec = showsPrec1

bindType_Expr :: (ty -> Type ty') -> Expr ty tm -> Expr ty' tm
bindType_Expr f e =
  case e of
    Var a -> Var a
    Name a -> Name a
    Let es b ->
      Let
        (fmap (bimap (fmap (bindType_Expr f)) (>>= f)) es)
        (bindType_Expr f b)
    Inst n ts -> Inst n ((>>= f) <$> ts)
    Ctor n ts -> Ctor n ((>>= f) <$> ts)
    Call a bs t ->
      Call (bindType_Expr f a) (bindType_Expr f <$> bs) (t >>= f)
    UInt8 ws -> UInt8 ws
    UInt16 ws -> UInt16 ws
    UInt32 ws -> UInt32 ws
    UInt64 ws -> UInt64 ws
    Int8 ws -> Int8 ws
    Int16 ws -> Int16 ws
    Int32 ws -> Int32 ws
    Int64 ws -> Int64 ws
    BTrue -> BTrue
    BFalse -> BFalse
    New a t -> New (bindType_Expr f a) (t >>= f)
    Deref a -> Deref $ bindType_Expr f a

newtype KMeta = KMeta Int
  deriving (Eq, Ord, Show)

data Kind = KType | KArr Kind Kind | KVar KMeta
  deriving (Eq, Ord, Show)

foldKMeta :: Monoid m => (KMeta -> m) -> Kind -> m
foldKMeta f k =
  case k of
    KType -> mempty
    KArr a b -> foldKMeta f a <> foldKMeta f b
    KVar a -> f a

substKMeta :: (KMeta -> Kind) -> Kind -> Kind
substKMeta f k =
  case k of
    KType -> KType
    KArr a b -> KArr (substKMeta f a) (substKMeta f b)
    KVar a -> f a

data Constraint a
  = CSized (Type a)
  | CForall (Maybe Text) Kind (Constraint (Var () a))
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

data Function
  = Function
  { funcName :: Text
  , funcTyArgs :: Vector (Text, Kind)
  , funcConstraints :: Vector (Constraint (Var Int Void)) -- indices from funcTyArgs
  , funcArgs :: Vector (Text, Type (Var Int Void)) -- indices from funcTyArgs
  , funcRetTy :: Type (Var Int Void) -- indices from funcTyArgs
  , funcBody ::
      Expr
        (Var Int Void) -- indices from funcTyArgs
        (Var Int Void) -- indices from funcArgs
  } deriving (Eq, Show)

data Constructor
  = Constructor
  { ctorName :: Text
  , ctorTyArgs :: Vector (Text, Kind)
  , ctorArgs :: Vector (Maybe Text, Type (Var Int Void))
  , ctorRetTy :: Type (Var Int Void)
  } deriving (Eq, Show)

data Datatype
  = Empty
  { datatypeName :: Text
  , datatypeTyArgs :: Vector (Text, Kind)
  }
  | Struct
  { datatypeName :: Text
  , datatypeTyArgs :: Vector (Text, Kind)
  , structFields :: Vector (Maybe Text, Type (Var Int Void))
  }
  | Enum
  { datatypeName :: Text
  , datatypeTyArgs :: Vector (Text, Kind)
  , enumCtors :: Vector (Text, Vector (Maybe Text, Type (Var Int Void)))
  } deriving (Eq, Show)

data Origin
  = ODatatype
  | OConstructor
  | OFunction
  deriving (Eq, Ord, Show)

data TypeScheme ty
  = TypeScheme
  { schemeOrigin :: Origin
  , schemeTyArgs :: Vector (Text, Kind)
  , schemeConstraints :: Vector (Constraint (Var Int ty)) -- indices from schemeTyArgs
  , schemeArgs :: Vector (Maybe Text, Type (Var Int ty)) -- indices from schemeTyArgs
  , schemeRetTy :: Type (Var Int ty) -- indices from schemeTyArgs
  }
deriveEq1 ''TypeScheme
deriveShow1 ''TypeScheme
instance Eq ty => Eq (TypeScheme ty) where; (==) = eq1
instance Show ty => Show (TypeScheme ty) where; showsPrec = showsPrec1

functionToTypeScheme :: Function -> TypeScheme Void
functionToTypeScheme (Function _ tyArgs constrs args ret _) =
  TypeScheme OFunction tyArgs constrs (over (mapped._1) Just args) ret

datatypeConstructors :: Datatype -> Vector Constructor
datatypeConstructors adt =
  case adt of
    Empty{} -> mempty
    Struct name params fields ->
      [ Constructor
        { ctorName = name
        , ctorTyArgs = params
        , ctorArgs = fields
        , ctorRetTy =
            foldl @[]
              (\a b -> TApp a (TVar $ B b))
              (TName name)
              [0..length params-1]
        }
      ]
    Enum name params ctors ->
      let
        retTy =
          foldl @[]
            (\a b -> TApp a (TVar $ B b))
            (TName name)
            [0..length params-1]
      in
        (\(cn, fields) ->
          Constructor
          { ctorName = cn
          , ctorTyArgs = params
          , ctorArgs = fields
          , ctorRetTy = retTy
          }
        ) <$>
        ctors

constructorToTypeScheme :: Constructor -> TypeScheme Void
constructorToTypeScheme (Constructor _ tyArgs args retTy) =
  TypeScheme
  { schemeOrigin = OConstructor
  , schemeTyArgs = tyArgs
  , schemeConstraints = []
  , schemeArgs = args
  , schemeRetTy = retTy
  }

data Declaration
  = DData Datatype
  | DCtor Constructor
  | DFunc Function

declOrigin :: Declaration -> Origin
declOrigin d =
  case d of
    DFunc{} -> OFunction
    DCtor{} -> OConstructor
    DData{} -> ODatatype

declName :: Declaration -> Text
declName d =
  case d of
    DFunc f -> funcName f
    DCtor c -> ctorName c
    DData a -> datatypeName a
