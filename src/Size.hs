{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
module Size
  ( Size(..), pattern Var, (.@), plusSize, maxSize
  , sizeConstraintFor
  )
where

import Bound ((>>>=), Scope, instantiate1)
import Bound.Var (Var(..))
import Control.Monad (ap)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Word (Word64)

import IR (Kind(..))
import qualified IR
import qualified Syntax

data Size a
  = Lam (Scope () Size a)
  | App a [Size a]
  | Plus (Size a) (Size a)
  | Max (Size a) (Size a)
  | Word Word64
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Size
deriveShow1 ''Size
instance Eq a => Eq (Size a) where; (==) = eq1
instance Show a => Show (Size a) where; showsPrec = showsPrec1
instance Applicative Size where; pure a = App a []; (<*>) = ap
instance Monad Size where -- probably not lawful, but it's helpful to have everything be 'beta-normal'
  Lam a >>= f = Lam (a >>>= f)
  App a bs >>= f = foldl (.@) (f a) ((>>= f) <$> bs)
  Plus a b >>= f =
    let
      a' = a >>= f
      b' = b >>= f
    in
      case (a', b') of
        (Word m, Word n) -> Word $! m + n
        _ -> Plus a' b'
  Max a b >>= f =
    let
      a' = a >>= f
      b' = b >>= f
    in
      case (a', b') of
        (Word m, Word n) -> Word $! max m n
        _ -> Plus a' b'
  Word n >>= _ = Word n

pattern Var :: a -> Size a
pattern Var a = App a []

infixl 5 .@
(.@) :: Size a -> Size a -> Size a
(.@) (Lam f) x = instantiate1 x f
(.@) (App a bs) x = App a (bs ++ [x])
(.@) Word{} _ = error "applying to Word"
(.@) Plus{} _ = error "applying to Plus"
(.@) Max{} _ = error "applying to Max"

plusSize :: Size a -> Size a -> Size a
plusSize (Word 0) b = b
plusSize a (Word 0) = a
plusSize (Word a) (Word b) = Word (a + b)
plusSize a b = Plus a b

maxSize :: Size a -> Size a -> Size a
maxSize (Word 0) b = b
maxSize a (Word 0) = a
maxSize (Word a) (Word b) = Word (max a b)
maxSize a b = Max a b

-- | Computes a size constraint for a type of a particular kind
--
-- Examples:
--
-- `Type` maps to `Sized #0`
-- `Type -> Type` maps to `forall t0. Sized t0 => Sized (#0 t0)`
-- `(Type -> Type) -> Type -> Type` maps to `forall t0. (forall t1. Sized t1 => Sized (t0 t1)) => forall t3. Sized t3 => Sized #0`
sizeConstraintFor ::
  Kind ->
  IR.Constraint (Var () ty)
sizeConstraintFor = go [] (B ())
  where
    go ::
      [x] ->
      x ->
      Kind ->
      IR.Constraint x
    go quants x k =
      case k of
        KType ->
          IR.CSized $
          foldl
            (\acc v -> Syntax.TApp Syntax.Unknown acc $ Syntax.TVar v)
            (Syntax.TVar x)
            quants
        KArr a b ->
          IR.CForall Nothing a $
          IR.CImplies (sizeConstraintFor a) $
          go (fmap F quants ++ [B ()]) (F x) b
        KVar m -> error $ show m <> " in sizeConstraintFor"
