module Size.Builtins
  ( builtins
  , ptrSize
  , boolSize
  , uintSizes
  , intSizes
  )
where

import Bound.Var (Var(..))
import Data.Void (Void)

import IR (Constraint(..), Kind(..))
import Size (Size)
import qualified Size
import Syntax (Type(..), wordSize, wordSizes)

builtins :: [(Constraint Void, Size Void)]
builtins =
  ptrSize :
  boolSize :
  uintSizes <>
  intSizes

ptrSize :: (Constraint Void, Size Void)
ptrSize =
  ( CForall Nothing KType $
    CSized $ TApp TPtr (TVar $ B ())
  , Size.Word 8
  )

boolSize :: (Constraint Void, Size Void)
boolSize =
  ( CSized TBool
  , Size.Word 1
  )

uintSizes :: [(Constraint Void, Size Void)]
uintSizes =
  (\ws ->
     ( CSized $ TUInt ws
     , Size.Word $ wordSize ws
     )
  ) <$>
  wordSizes

intSizes :: [(Constraint Void, Size Void)]
intSizes =
  (\ws ->
     ( CSized $ TInt ws
     , Size.Word $ wordSize ws
     )
  ) <$>
  wordSizes
