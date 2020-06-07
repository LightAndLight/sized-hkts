{-# language BangPatterns #-}
{-# language DeriveGeneric #-}
{-# language MagicHash, UnboxedSums, UnboxedTuples #-}
module Parser where

import Control.Applicative (Alternative(..))
import Control.DeepSeq (NFData)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text ()
import Data.Text.Array (Array(..))
import Data.Text.Internal (Text(Text))
import Data.Text.Internal.Encoding.Utf16 (chr2)
import Data.Text.Internal.Unsafe.Char (unsafeChr)
import GHC.Exts
  ( ByteArray#, Int#
  , (<#), (<=#), (>#), (+#)
  , andI#, indexWord16Array#
  , orI#, word2Int#
  )
import GHC.Generics (Generic)
import GHC.Int (Int(I#))
import GHC.Word (Word16(W16#))

type Input = ByteArray#
type ByteOffset = Int#
type CharOffset = Int#
type ByteLength = Int#

type State = (# Input, ByteOffset, ByteLength, CharOffset #)

{-# inline makeState #-}
makeState ::
  Input ->
  ByteOffset ->
  ByteLength ->
  CharOffset ->
  State
makeState i bo bl co = (# i, bo, bl, co #)

{-# inline input #-}
input :: State -> Input
input (# i, _, _, _ #) = i

{-# inline byteOffset #-}
byteOffset :: State -> ByteOffset
byteOffset (# _, bo, _, _ #) = bo

{-# inline addByteOffset #-}
addByteOffset :: Int# -> State -> State
addByteOffset n (# i, bo, bl, co #) = (# i, n +# bo, bl, co #)

{-# inline charOffset #-}
charOffset :: State -> CharOffset
charOffset (# _, _, _, co #) = co

{-# inline addCharOffset #-}
addCharOffset :: Int# -> State -> State
addCharOffset n (# i, bo, bl, co #) = (# i, bo, bl, n +# co #)

{-# inline addByteCharOffset #-}
addByteCharOffset :: Int# -> Int# -> State -> State
addByteCharOffset m n (# i, bo, bl, co #) = (# i, m +# bo, bl, n +# co #)

{-# inline byteLength #-}
byteLength :: State -> ByteLength
byteLength (# _, _, bl, _ #) = bl

-- | Ported from Data.Text.Unsafe
{-# inline iter #-}
iter :: State -> (# Char, State #)
iter state =
  case orI# ((<#) (word2Int# m) 0xD800#) ((>#) (word2Int# m) 0xDBFF#) of
    0# ->
      (# chr2 (W16# m) (W16# n)
      -- , addCharOffset (int2Word# 1#) (addByteOffset (int2Word# 2#) state)
      , addByteCharOffset 2# 1# state
      #)
    _ ->
      (# unsafeChr (W16# m)
      -- , addCharOffset (int2Word# 1#) (addByteOffset (int2Word# 1#) state)
      , addByteCharOffset 1# 1# state
      #)
  where
    m = indexWord16Array# (input state) j
    n = indexWord16Array# (input state) k
    j = byteOffset state
    k = j +# 1#

data ParseError
  = Unexpected Int (Set Char) Bool
  | Empty
  deriving (Eq, Show, Generic)

instance NFData ParseError

type Consumed = Int#
type StartSet = (# Set Char, Bool #)
type Nullable = Int#

newtype Parser a
  = Parser
    { unParser ::
        (# StartSet, State #) ->
        (#
          (# Consumed, Nullable, StartSet, ParseError #) |
          (# Consumed, Nullable, StartSet, State, a #)
        #)
    }

parse :: Parser a -> Text -> Either ParseError a
parse (Parser p) (Text (Array arr) (I# off) (I# len)) =
  case p (# (# Set.empty, False #), makeState arr off len 0# #) of
    (# (# _, _, _, e #) | #) -> Left e
    (# | (# _, _, _, _, res #) #) -> Right res

instance Functor Parser where
  fmap f (Parser p) =
    Parser $ \state ->
    case p state of
      (# e | #) -> (# e | #)
      (# | (# consumed, nullable, ss, state', result #) #) ->
        (# | (# consumed, nullable, ss, state', f result #) #)

instance Applicative Parser where
  pure a = Parser $ \(# ss, state #) -> (# | (# 0#, 1#, ss, state, a #) #)
  {-# inline (<*>) #-}
  Parser pf <*> Parser pa =
    Parser $ \(# ss, state #) ->
    case pf (# ss, state #) of
      (# e | #) -> (# e | #)
      (# | (# consumed, nullable, ss', state', f #) #) ->
        case pa (# ss', state' #) of
          (# (# consumed', nullable', ss'', e #) | #) ->
            (# (# orI# consumed consumed', andI# nullable nullable', ss'', e #) | #)
          (# | (# consumed', nullable', ss'', state'', a #) #) ->
            (# | (# orI# consumed consumed', andI# nullable nullable', ss'', state'', f a #) #)

instance Alternative Parser where
  empty = Parser $ \_ -> (# (# 0#, 0#, (# Set.empty, False #), Empty #) | #)
  {-# inline (<|>) #-}
  Parser pa <|> Parser pb =
    Parser $ \(# ss, state #) ->
    case pa (# ss, state #) of
      (# (# consumed, nullable, ss', e #) | #) ->
        case consumed of
          1# -> (# (# consumed, nullable, ss', e #) | #)
          _ ->
            case pb (# ss', state #) of
              (# (# consumed', nullable', ss'', e' #) | #) ->
                (# (# consumed', orI# nullable nullable', ss'', e' #) | #)
              (# | (# consumed', nullable', ss'', state', res #) #) ->
                (# | (# consumed', orI# nullable nullable', ss'', state', res #) #)
      (# | (# _, ss'', nullable, state', a #) #) ->
        (# | (# 1#, ss'', nullable, state', a #) #)

instance Monad Parser where
  Parser pa >>= f =
    Parser $ \(# ss, state #) ->
    case pa (# ss, state #) of
      (# e | #) -> (# e | #)
      (# | (# consumed, nullable, ss', state', a #) #) ->
        case unParser (f a) (# ss', state' #) of
          (# (# consumed', nullable', ss'', e #) | #) ->
            (# (# orI# consumed consumed', andI# nullable nullable', ss'', e #) | #)
          (# | (# consumed', nullable', ss'', state'', res #) #) ->
            (# | (# orI# consumed consumed', andI# nullable nullable', ss'', state'', res #) #)

{-# inline char #-}
char :: Char -> Parser ()
char c =
  Parser $
  \(# (# ss, expectsEof #), state #) ->
  let
    !ss' = Set.insert c ss
  in
    case (<=#) (byteOffset state) (byteLength state) of
      1# ->
        case iter state of
          (# c', state' #) ->
            case c == c' of
              False ->
                (# (# 0#, 0#, (# ss', expectsEof #), Unexpected (I# (charOffset state)) ss' expectsEof #) | #)
              True ->
                (# |
                  (# 1#
                  , 0#
                  , (# Set.empty, False #)
                  , state'
                  , ()
                  #)
                #)
      _ -> (# (# 0#, 0#, (# ss', expectsEof #), Unexpected (I# (charOffset state)) ss' expectsEof #) | #)

try :: Parser a -> Parser a
try (Parser p) =
  Parser $
  \(# ss, state #) ->
  case p (# ss, state #) of
    (# (# _, _, ss', e #) | #) ->
      (# (# 0#, 1#, ss', e #) | #)
    (# | (# consumed, _, ss', state', res #) #) ->
      (# | (# consumed, 1#, ss', state', res #) #)

eof :: Parser ()
eof =
  Parser $
  \(# (# ss, _ #), state #) ->
  case (<=#) (byteOffset state) (byteLength state) of
    1# -> (# (# 0#, 1#, (# ss, True #) , Unexpected (I# (charOffset state)) ss True #) | #)
    _ -> (# | (# 0#, 1#, (# ss, True #), state, () #) #)
