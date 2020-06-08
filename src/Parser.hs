{-# language BangPatterns #-}
{-# language DeriveGeneric #-}
{-# language MagicHash, UnboxedSums, UnboxedTuples #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
module Parser where

import Control.Applicative (Alternative(..))
import Control.DeepSeq (NFData)
import Data.Primitive.MachDeps (sIZEOF_INT)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text ()
import Data.Text.Array (Array(..))
import Data.Text.Internal (Text(Text))
import Data.Text.Internal.Encoding.Utf16 (chr2)
import Data.Text.Internal.Unsafe.Char (unsafeChr)
import GHC.Exts
  ( ByteArray#, Int#, MutableByteArray#, State#, RealWorld
  , (<#), (<=#), (>#), (+#), (*#)
  , indexWord16Array#
  , newByteArray#, readWord8ArrayAsInt#, writeWord8ArrayAsInt#
  , orI#, word2Int#
  , runRW#
  )
import GHC.Generics (Generic)
import GHC.Int (Int(I#))
import GHC.Word (Word16(W16#))

type Input = ByteArray#
type ByteOffset = Int#
type CharOffset = Int#
type ByteLength = Int#

type State = (# ByteOffset, ByteLength, CharOffset #)

{-

               sizeof_int                          3*sizeof_int
                   |                                     |
0                  v                                     v
| byteOffset: Int# | byteLength: Int# | charOffset: Int# |
                                      ^
                                      |
                                 2*sizeof_int

-}
type MState s = MutableByteArray# s

newMState :: (# ByteOffset, ByteLength, CharOffset #) -> State# s -> (# State# s, MState s #)
readState :: MState s -> State# s -> (# State# s, (# ByteOffset, ByteLength, CharOffset #) #)
writeState :: MState s -> (# ByteOffset, ByteLength, CharOffset #) -> State# s -> State# s
writeByteOffset, writeByteLength, writeCharOffset :: MState s -> Int# -> State# s -> State# s
(newMState, readState, writeState, writeByteOffset, writeByteLength, writeCharOffset) =
  (newMState_, readState_, writeState_, writeByteOffset_, writeByteLength_, writeCharOffset_)
  where
    sizeof_int =
      case sIZEOF_INT of
        I# i -> i

    boOffset =
      0#

    blOffset =
      sizeof_int

    coOffset =
      2# *# sizeof_int

    mstateSize = 3# *# sizeof_int

    writeState_ :: MState s -> (# ByteOffset, ByteLength, CharOffset #) -> State# s -> State# s
    writeState_ mstate (# bo, bl, co #) s =
      let
        s' = writeByteOffset_ mstate bo s
        s'' = writeByteLength_ mstate bl s'
        s''' = writeCharOffset_ mstate co s''
      in
        s'''

    newMState_ :: (# ByteOffset, ByteLength, CharOffset #) -> State# s -> (# State# s, MState s #)
    newMState_ val s =
      case newByteArray# mstateSize s of
        (# s', mstate #) ->
          let
            s'' = writeState mstate val s'
          in
            (# s'', mstate #)

    readState_ :: MState s -> State# s -> (# State# s, (# ByteOffset, ByteLength, CharOffset #) #)
    readState_ mstate s =
      case readWord8ArrayAsInt# mstate boOffset s of
        (# s', bo #) ->
          case readWord8ArrayAsInt# mstate blOffset s' of
            (# s'', bl #) ->
              case readWord8ArrayAsInt# mstate coOffset s'' of
                (# s''', co #) ->
                  (# s''', (# bo, bl, co #) #)

    writeByteOffset_ :: MState s -> Int# -> State# s -> State# s
    writeByteOffset_ mstate val s = writeWord8ArrayAsInt# mstate boOffset val s

    writeByteLength_ :: MState s -> Int# -> State# s -> State# s
    writeByteLength_ mstate val s = writeWord8ArrayAsInt# mstate blOffset val s

    writeCharOffset_ :: MState s -> Int# -> State# s -> State# s
    writeCharOffset_ mstate val s = writeWord8ArrayAsInt# mstate coOffset val s

{-# inline byteOffset #-}
byteOffset :: State -> ByteOffset
byteOffset (# bo, _, _ #) = bo

{-# inline charOffset #-}
charOffset :: State -> CharOffset
charOffset (# _, _, co #) = co

{-# inline addByteCharOffset #-}
addByteCharOffset :: Int# -> Int# -> State -> State
addByteCharOffset m n (# bo, bl, co #) = (# m +# bo, bl, n +# co #)

{-# inline byteLength #-}
byteLength :: State -> ByteLength
byteLength (# _, bl, _ #) = bl

-- | Ported from Data.Text.Unsafe
{-# inline iter #-}
iter :: (# Input, State #) -> (# Char, State #)
iter (# input, state #) =
  case orI# ((<#) (word2Int# m) 0xD800#) ((>#) (word2Int# m) 0xDBFF#) of
    0# ->
      (# chr2 (W16# m) (W16# n)
      , addByteCharOffset 2# 1# state
      #)
    _ ->
      (# unsafeChr (W16# m)
      , addByteCharOffset 1# 1# state
      #)
  where
    m = indexWord16Array# input j
    n = indexWord16Array# input k
    j = byteOffset state
    k = j +# 1#

data Label
  = Named Text
  | Char Char
  deriving (Eq, Ord, Show, Generic)

instance NFData Label

data ParseError
  = Unexpected Int (Set Label) Bool
  | Empty
  deriving (Eq, Show, Generic)

instance NFData ParseError

type Consumed = Int#
type StartSet = (# [Label], Bool #)

newtype Parser s a
  = Parser
    { unParser ::
        (# StartSet, Input, MState s, State# s #) ->
        (# State# s, Consumed, StartSet, (# ParseError | a #) #)
    }

{-# inline parse #-}
parse :: forall a. (forall s. Parser s a) -> Text -> Either ParseError a
parse (Parser p) (Text (Array arr) (I# off) (I# len)) =
  case runRW# run of
    (# _, _, _, output #) ->
      case output of
        (# e | #) -> Left e
        (# | res #) -> Right res
  where
    run :: State# RealWorld -> (# State# RealWorld, Consumed, StartSet, (# ParseError | a #) #)
    run s =
      case newMState (# off, len, 0# #) s of
        (# s', mstate #) ->
          p (# (# mempty, False #), arr, mstate, s' #)

instance Functor (Parser s) where
  fmap f (Parser p) =
    Parser $ \state ->
    case p state of
      (# consumed, ss, s, output #) ->
        (# consumed
        , ss
        , s
        , case output of
            (# e | #) ->
              (# e | #)
            (# | result #) ->
              (# | f result #)
        #)

instance Applicative (Parser s) where
  pure a = Parser $ \(# ss, _, _, s #) -> (# s, 0#, ss, (# | a #) #)
  {-# inline (<*>) #-}
  Parser pf <*> Parser pa =
    Parser $ \(# ss, input, state, s #) ->
    case pf (# ss, input, state, s #) of
      (# s', consumed, ss', output #) ->
        case output of
          (# e | #) -> (# s', consumed, ss', (# e | #) #)
          (# | f #) ->
            case pa (# ss', input, state, s' #) of
              (# s'', consumed', ss'', output' #) ->
                case output' of
                  (# e | #) ->
                    (# s'', orI# consumed consumed', ss'', (# e | #) #)
                  (# | a #) ->
                    (# s'', orI# consumed consumed', ss'', (# | f a #) #)

instance Alternative (Parser s) where
  empty = Parser $ \(# _, _, _, s #) -> (# s, 0#, (# mempty, False #), (# Empty | #) #)
  {-# inline (<|>) #-}
  Parser pa <|> Parser pb =
    Parser $ \(# ss, input, state, s #) ->
    case pa (# ss, input, state, s #) of
      (# s', consumed, ss', output #) ->
        case consumed of
          1# -> (# s', consumed, ss', output #)
          _ ->
            case output of
              (# | _ #) -> (# s', 1#, ss', output #)
              (# _ | #) ->
                case pb (# ss', input, state, s' #) of
                  (# s'', consumed', ss'', output' #) ->
                    (# s'', consumed', ss'', output' #)

instance Monad (Parser s) where
  Parser pa >>= f =
    Parser $ \(# ss, input, state, s #) ->
    case pa (# ss, input, state, s #) of
      (# s', consumed, ss', output #) ->
        case output of
          (# e | #) -> (# s', consumed, ss', (# e | #) #)
          (# | a #) ->
            case unParser (f a) (# ss', input, state, s' #) of
             (# s'', consumed', ss'', output' #) ->
               (# s'', orI# consumed consumed', ss'', output' #)

{-# inline char #-}
char :: Char -> Parser s ()
char c =
  Parser $
  \(# (# ss, expectsEof #), input, state, s #) ->
  let ss' = Char c : ss in
  case readState state s of
    (# s', state_ #) ->
      case (<=#) (byteOffset state_) (byteLength state_) of
        1# ->
          case iter (# input, state_ #) of
            (# c', state_' #) ->
              case c == c' of
                False ->
                  (# s'
                  , 0#
                  , (# ss', expectsEof #)
                  , (# Unexpected (I# (charOffset state_)) (Set.fromList ss') expectsEof | #)
                  #)
                True ->
                  case writeState state state_' s' of
                    s'' ->
                      (# s''
                      , 1#
                      , (# mempty, False #)
                      , (# | () #)
                      #)
        _ ->
          (# s'
          , 0#
          , (# ss', expectsEof #)
          , (# Unexpected (I# (charOffset state_)) (Set.fromList ss') expectsEof | #)
          #)

try :: Parser s a -> Parser s a
try (Parser p) =
  Parser $
  \(# ss, input, state, s #) ->
  case p (# ss, input, state, s #) of
    (# s', consumed, ss', output #) ->
      case output of
        (# _ | #) -> (# s', 0#, ss', output #)
        (# | _ #) -> (# s', consumed, ss', output #)

eof :: Parser s ()
eof =
  Parser $
  \(# (# ss, _ #), _, state, s #) ->
  case readState state s of
    (# s', state_ #) ->
      case (<=#) (byteOffset state_) (byteLength state_) of
        1# ->
          (# s', 0#, (# ss, True #) , (# Unexpected (I# (charOffset state_)) (Set.fromList ss) True | #) #)
        _ ->
          (# s', 0#, (# ss, True #), (# | () #) #)

infixl 4 <?>
(<?>) :: Parser s a -> Text -> Parser s a
(<?>) (Parser p) name =
  Parser $ \(# (# ss, expectsEof #), input, state, s #) ->
  case p (# (# ss, expectsEof #), input, state, s #) of
    (# s', consumed, _, output #) ->
      let
        ss' = Named name : ss
      in
        (# s'
        , consumed
        , (# ss', expectsEof #)
        , case output of
            (# Unexpected pos _ _ | #) ->
              (# Unexpected pos (Set.fromList ss') expectsEof | #)
            _ -> output
        #)
