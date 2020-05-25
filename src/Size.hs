{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
module Size where

import Bound ((>>>=), Scope, instantiate1)
import Control.Monad (ap)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Word (Word64)

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

