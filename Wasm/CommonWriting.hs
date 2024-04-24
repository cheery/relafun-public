module Wasm.CommonWriting where

import Data.Bits
import Data.Word
import Data.Text.Encoding (encodeUtf8)
import qualified Data.ByteString as B
import qualified Data.Text as T

writeFile :: Writable t => FilePath -> t -> IO ()
writeFile n t = B.writeFile n (B.pack (write t))

class Writable t where
  write :: t -> [Word8]

instance Writable Word8 where
  write = pure

utf8 :: String -> [Word8]
utf8 = vec . B.unpack . encodeUtf8 . T.pack

vec' :: (a -> [Word8]) -> [a] -> [Word8]
vec' f b = u32 (length b) <> concat (map f b)

vec :: Writable a => [a] -> [Word8]
vec b = u32 (length b) <> concat (map write b)

u32 :: Integral a => a -> [Word8]
u32 = leb128 . fromIntegral

s32 :: Integral a => a -> [Word8]
s32 = sleb128 . fromIntegral

leb128 :: Integer -> [Word8]
leb128 n
  | n < 0     = error "uleb128 got negative value"
  | m == 0    = [byte]
  | otherwise = (byte .|. 0x80) : leb128 m
  where
    byte = fromIntegral (n .&. 0x7F)
    m    = n `shiftR` 7

sleb128 :: Integer -> [Word8]
sleb128 n
  | m == (-1) = [byte]
  | m == 0    = [byte]
  | otherwise = (byte .|. 0x80) : sleb128 m
  where
    byte = fromIntegral (n .&. 0x7F)
    m    = n `shiftR` 7
