{-# language MagicHash, UnboxedSums, UnboxedTuples #-}
module Parser where

import Data.Text.Internal.Encoding.Utf16 (chr2)
import Data.Text.Internal.Unsafe.Char (unsafeChr)
import GHC.Exts
  ( ByteArray#, Word#
  , (<#), (>#)
  , indexWord16Array#, int2Word#
  , leWord#, orI#, plusWord#, word2Int#
  )
import GHC.Word (Word16(W16#), Word64(W64#))

type Input = ByteArray#
type Offset = Word#
type Length = Word#

type State = (# Input, Offset, Length #)

input :: State -> Input
input (# i, _, _ #) = i

offset :: State -> Offset
offset (# _, o, _ #) = o

addOffset :: Word# -> State -> State
addOffset n (# i, o, l #) = (# i, plusWord# n o, l #)

len :: State -> Length
len (# _, _, l #) = l

-- | Ported from Data.Text.Unsafe
iter :: State -> (# Char, State #)
iter state =
  case orI# ((<#) (word2Int# m) 0xD800#) ((>#) (word2Int# m) 0xDBFF#) of
    0# -> (# chr2 (W16# m) (W16# n), addOffset (int2Word# 2#) state #)
    _ -> (# unsafeChr (W16# m), addOffset (int2Word# 1#) state #)
  where
    m = indexWord16Array# (input state) (word2Int# j)
    n = indexWord16Array# (input state) (word2Int# k)
    j = offset state
    k = j `plusWord#` int2Word# 1#


data ParseError
  = UnexpectedEof Word64

newtype Parser a
  = Parser
  { unParser ::
      State ->
      (# ParseError | (# State, a #) #)
  }

instance Functor Parser where
  fmap f (Parser p) =
    Parser $ \state ->
    case p state of
      (# e | #) -> (# e | #)
      (# | (# state', result #) #) -> (# | (# state', f result #) #)

instance Applicative Parser where
  pure a = Parser $ \state -> (# | (# state, a #) #)
  Parser pf <*> Parser pa =
    Parser $ \state ->
    case pf state of
      (# e | #) -> (# e | #)
      (# | (# state', f #) #) ->
        case pa state' of
          (# e | #) -> (# e | #)
          (# | (# state'', a #) #) ->
            (# | (# state'', f a #) #)

instance Monad Parser where
  Parser p >>= f =
    Parser $ \state ->
    case p state of
      (# e | #) -> (# e | #)
      (# | (# state', a #) #) ->
        unParser (f a) state'

anyChar :: Parser Char
anyChar =
  Parser $ \state ->
  case leWord# (offset state) (len state) of
    0# -> (# UnexpectedEof (W64# (offset state)) | #)
    _ ->
      case iter state of
        (# c, state' #) -> (# | (# state', c #) #)
