{-# LANGUAGE TypeFamilies #-}
module Lib.Parser where

import Control.Applicative (Alternative (..))
import Data.List (nub)
import Data.Word (Word8)

data Proxy a = Proxy

class Item a where
  type Pos a
  initPos :: Proxy a -> Pos a
  step :: a -> Pos a -> Pos a

instance Item Char where
  type Pos Char = (Int, Int)
  initPos _ = (1, 1)
  step '\n' (line,col) = (line+1, 1)
  step _    (line,col) = (line, col+1)

instance Item Word8 where
  type Pos Word8 = Int
  initPos _ = 0
  step _ pos = pos+1

class Eq e => ParseError e where
  type EItem e
  endOfInput :: e
  unexpected :: EItem e -> e
  noParse :: e

type Parser e a = FParser e (EItem e) (Pos (EItem e)) a

newtype FParser e s p a = Parser
  { runParser :: [s] -> p -> Either [(e, p)] (a, [s], p) }

satisfy :: (ParseError e, EItem e ~ s, Item s) => (s -> Bool) -> FParser e s (Pos s) s
satisfy p = Parser go
  where go [] pos = Left [(endOfInput, pos)]
        go (hd : rest) pos | p hd = Right (hd, rest, step hd pos)
                           | otherwise = Left [(unexpected hd, pos)]

getPos :: Parser e (Pos (EItem e))
getPos = Parser go where go ss pos = Right (pos, ss, pos)

takeN :: (ParseError e, EItem e ~ s, Item s) => Int -> FParser e s (Pos s) [s]
takeN i = Parser go
  where go ss pos = let taken = take i ss
                        remain = drop i ss
                        pos' = foldl (flip step) pos taken
                    in if length taken == i
                       then Right (taken, remain, pos')
                       else Left [(endOfInput, pos')]

eof :: (ParseError e, EItem e ~ s) => FParser e s (Pos s) ()
eof = Parser go
  where go [] pos = Right ((), [], pos)
        go (hd:_) pos = Left [(unexpected hd, pos)]

item :: (Eq s, ParseError e, EItem e ~ s, Item s) => s -> FParser e s (Pos s) s
item i = satisfy (== i)

instance Functor (FParser e s p) where
  fmap f (Parser p) = Parser (\input pos -> q (p input pos))
    where q (Left err) = Left err
          q (Right (o, rest, pos)) = Right (f o, rest, pos)

instance Applicative (FParser e s p) where
  pure a = Parser (\rest pos -> Right (a, rest, pos))
  Parser f <*> Parser p = Parser $ \input pos -> do
    (f', rest, pos') <- f input pos
    (x, rest', pos'') <- p rest pos'
    pure (f' x, rest', pos'')

instance Monad (FParser e s p) where
  Parser p >>= k = Parser $ \input pos -> do
    (x, rest, pos') <- p input pos
    runParser (k x) rest pos'

items :: (Eq s, ParseError e, EItem e ~ s, Item s) => [s] -> FParser e s (Pos s) [s]
items = traverse item

instance (ParseError e, EItem e ~ s, Ord p) => Alternative (FParser e s p) where
  empty = Parser (\_ pos -> Left [(noParse, pos)])

  Parser l <|> Parser r = Parser $ \input pos ->
    case l input pos of
      Left err -> case r input pos of
                       Left err' -> Left (knub (err <> err'))
                       Right a -> Right a
      Right a -> Right a

knub :: (Eq a, Ord b) => [(a, b)] -> [(a, b)]
knub err = (nub . filter ((==h) . snd)) err
  where h = (maximum . map snd) err

sepBy :: Alternative f => f a -> f s -> f [a]
sepBy thing sep = sepBy1 thing sep <|> pure []

sepBy1 :: Alternative f => f a -> f s -> f [a]
sepBy1 thing sep = (:) <$> (thing <* sep) <*> (sepBy thing sep) <|> pure <$> thing

perhaps :: (a -> Either e b) -> FParser e s p a -> FParser e s p b
perhaps f (Parser p) = Parser (\input pos -> go (p input pos) pos)
  where go (Left err) pos = Left err
        go (Right (x, rest, pos)) posA = case f x of
           Left err -> Left [(err, posA)]
           Right y -> Right (y, rest, pos)

quickParse :: forall e s a. Item s => FParser e s (Pos s) a -> [s] -> Either [(e, Pos s)] a
quickParse p s = q (runParser p s (initPos (Proxy :: Proxy s)))
  where q (Left err) = Left err
        q (Right (a,_,_)) = Right a

subParse :: (ParseError e, Item (EItem e)) => Int -> Parser e a -> Parser e a
subParse i p = do
  pos <- getPos
  ss <- takeN i
  Parser (\inp pos' -> case runParser p ss pos of
                            Left err -> Left err
                            Right (a,_,_) -> Right (a, inp, pos'))

nTimes :: (ParseError e, Item (EItem e)) => Int -> Parser e a -> Parser e [a]
nTimes 0 p = pure []
nTimes n p = do one <- p
                rest <- nTimes (n-1) p
                pure (one:rest)
