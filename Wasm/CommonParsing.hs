{-# LANGUAGE TypeFamilies #-}
module Wasm.CommonParsing where

import Data.Bits
import Data.Text.Encoding (decodeUtf8)
import Data.Word (Word8)
import Lib.Parser
import qualified Data.ByteString as B
import qualified Data.Text as T

data SyntaxError
  = EndOfInput
  | Unexpected Word8
  | NoParse
  deriving (Eq, Show)

instance ParseError SyntaxError where
  type EItem SyntaxError = Word8
  endOfInput = EndOfInput
  unexpected = Unexpected
  noParse = NoParse

type Readable a = Parser SyntaxError a

section :: (Word8 -> Readable a) -> Readable a
section p = do n <- byte
               size <- u32
               subParse size (p n <* eof)

vec :: Readable a -> Readable [a]
vec p = do n <- u32
           nTimes n p

s32, u32 :: Num a => Readable a
s32 = fromIntegral <$> sleb128
u32 = fromIntegral <$> leb128

byte :: Readable Word8
byte = satisfy (\_ -> True)

leb128 :: Readable Integer
leb128 = go (0 :: Integer) 0
  where go result shift
          = do byte <- satisfy (\_ -> True)
               let r = result .|. ((fromIntegral byte .&. 0x7F) `shiftL` shift)
                   s = shift + 7
               if (0x80 .&. byte) == 0
                 then pure r
                 else go r s

sleb128 :: Readable Integer
sleb128 = go (0 :: Integer) 0
  where go result shift
          = do byte <- satisfy (\_ -> True)
               let r = result .|. ((fromIntegral byte .&. 0x7F) `shiftL` shift)
                   s = shift + 7
               if (0x80 .&. byte) == 0
                   then if (byte .&. 0x40) /= 0
                        then pure $ r .|. (-1 `shiftL` s)
                        else pure r
                   else go r s

utf8 :: Readable String
utf8 = do n <- u32
          s <- takeN n
          pure $ T.unpack $ decodeUtf8 $ B.pack s

f32, f64 :: Readable [Word8]
f32 = takeN 4
f64 = takeN 8
