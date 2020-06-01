module Size.Builtins
  ( builtins
  , ptrSize
  , boolSize
  , int32Size
  )
where

import Bound.Var (Var(..))
import Data.Void (Void)

import IR (Constraint(..), Kind(..))
import Size (Size)
import qualified Size
import Syntax (Type(..))

builtins :: [(Constraint Void, Size Void)]
builtins =
  ptrSize :
  boolSize :
  int32Size :
  []

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

int32Size :: (Constraint Void, Size Void)
int32Size =
  ( CSized TInt32
  , Size.Word 4
  )
