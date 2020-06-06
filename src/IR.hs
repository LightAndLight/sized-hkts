{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language OverloadedLists, OverloadedStrings #-}
{-# language TemplateHaskell #-}
{-# language TypeApplications #-}
module IR where

import Bound.Var (Var(..), unvar)
import Control.Lens.Setter (over, mapped)
import Control.Lens.Tuple (_1)
import Data.Bifunctor (bimap)
import Data.Deriving (deriveEq1, deriveOrd1, deriveShow1, deriveEq2, deriveShow2)
import Data.Functor.Classes (Eq1(..), Show1(..), Eq2(..), Show2(..), eq1, compare1, showsPrec1)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Void (Void)
import Data.Word (Word8, Word64)
import Data.Int (Int32)
import qualified Data.Text.Read as Text (decimal)

import Syntax (Type(..))

data Projection
  = Numeric Word64
  | Field Text
  deriving (Eq, Show)

parseProjection :: Text -> Projection
parseProjection a =
  case Text.decimal a of
    Right (n, "") -> Numeric n
    _ -> Field a

data Case ty tm
  = Case
  { caseCtor :: Text
  , caseArgs :: Vector Text
  , caseExpr :: Expr ty (Var Int tm)
  } deriving (Functor, Foldable, Traversable)

data Expr ty tm
  = Var tm
  | Name Text

  | Let (Vector ((Text, Expr ty tm), Type ty)) (Expr ty tm)
  | Inst Text (Vector (Type ty))
  | Ctor Text (Vector (Type ty))
  | Call (Expr ty tm) (Vector (Expr ty tm)) (Type ty)

  | Int32 Int32

  | BTrue
  | BFalse

  | New (Expr ty tm) (Type ty)
  | Deref (Expr ty tm)

  | Project (Expr ty tm) Projection
  | Match (Expr ty tm) (Type ty) (Vector (Case ty tm)) (Type ty)
  deriving (Functor, Foldable, Traversable)
deriveEq2 ''Case
deriveShow2 ''Case
instance (Eq ty) => Eq1 (Case ty) where; liftEq = liftEq2 (==)
instance (Show ty) => Show1 (Case ty) where; liftShowsPrec = liftShowsPrec2 showsPrec showList
instance (Eq ty, Eq tm) => Eq (Case ty tm) where; (==) = eq1
instance (Show ty, Show tm) => Show (Case ty tm) where; showsPrec = showsPrec1

deriveEq2 ''Expr
deriveShow2 ''Expr
instance (Eq ty) => Eq1 (Expr ty) where; liftEq = liftEq2 (==)
instance (Show ty) => Show1 (Expr ty) where; liftShowsPrec = liftShowsPrec2 showsPrec showList
instance (Eq ty, Eq tm) => Eq (Expr ty tm) where; (==) = eq1
instance (Show ty, Show tm) => Show (Expr ty tm) where; showsPrec = showsPrec1

bindType_Case :: (ty -> Type ty') -> Case ty tm -> Case ty' tm
bindType_Case f (Case name args e) =
  Case name args (bindType_Expr f e)

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
    Int32 ws -> Int32 ws
    BTrue -> BTrue
    BFalse -> BFalse
    New a t -> New (bindType_Expr f a) (t >>= f)
    Deref a -> Deref $ bindType_Expr f a
    Project a b -> Project (bindType_Expr f a) b
    Match a inTy bs resTy ->
      Match (bindType_Expr f a) (inTy >>= f) (bindType_Case f <$> bs) (resTy >>= f)

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

data CtorSort
  = StructCtor
  | EnumCtor Word8
  deriving (Eq, Show)

data Constructor
  = Constructor
  { ctorName :: Text
  , ctorSort :: CtorSort
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

data Fields
  = Unnamed (Vector (Type (Var Int Void)))
  | Named (Map Text (Type (Var Int Void)))
  deriving Show

makeDatatypeFields :: Datatype -> Maybe Fields
makeDatatypeFields adt =
  case adt of
    Empty{} -> Just $ Unnamed mempty
    Struct _ _ fs -> Just . either (Unnamed . Vector.fromList) Named $ namedOrUnnamed fs
    Enum{} -> Nothing
  where
    namedOrUnnamed =
      Maybe.fromJust .
      foldr
        (\(m_n, t) rest ->
          case rest of
            Nothing ->
              Just $
              maybe
                (Left [t])
                (\n -> Right $ Map.singleton n t)
                m_n
            Just (Left unnamed) ->
              case m_n of
                Just{} -> error $ "makeDatatypeFields: mix of named an unnamed fields in " <> show adt
                Nothing -> Just . Left $ t : unnamed
            Just (Right named) ->
              case m_n of
                Nothing -> error $ "makeDatatypeFields: mix of named an unnamed fields in " <> show adt
                Just n -> Just . Right $ Map.insert n t named
        )
        Nothing

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
        , ctorSort = StructCtor
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
        (\(tag, (cn, fields)) ->
          Constructor
          { ctorName = cn
          , ctorSort = EnumCtor tag
          , ctorTyArgs = params
          , ctorArgs = fields
          , ctorRetTy = retTy
          }
        ) <$>
        Vector.zip [0..] ctors

constructorToTypeScheme :: Constructor -> TypeScheme Void
constructorToTypeScheme (Constructor _ _ tyArgs args retTy) =
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
  deriving Show

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
