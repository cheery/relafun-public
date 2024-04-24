{-# LANGUAGE TypeFamilies #-}
module Syntax where

import Control.Applicative (Alternative (..))
import Data.Char
import Data.List (elemIndex)
import qualified Data.Set as S
import Lib.Parser
import qualified Text.PrettyPrint as P

data SyntaxError
  = EndOfInput
  | Unexpected Char
  | ExpectedIdentifier [Char]
  | ExpectedGot [Char] [Char]
  | NoParse
  deriving (Eq, Show)

type FileSyntax = (String, [DeclarationSyntax])

data DeclarationSyntax
  = Definition Name Term
  deriving (Show)

data Term
  = Lam Name Term
  | App Term Term
  | Let Name Term Term
  | Sym Name
  | Var DeBruijnIndex
  | Lit Integer
  deriving (Show)

type Name = String
type DeBruijnIndex = Int

type Absents = S.Set String
data PType a = Con String
             | TApp (PType a) (PType a)
             | Meta a
             | RMeta Absents a
             | RField String (PType a) (PType a)
             | RClosed
  deriving (Eq, Ord)

show_type :: Show a => Int -> PType a -> P.Doc
show_type r (Con s) = P.text s
show_type r (TApp (TApp (Con "->") a) b) = P.text "(" <> show_type r a <> P.text " -> " <> show_type r b <> P.text ")"
show_type r (TApp a b) = P.text "(" <> show_type r a <> P.text " " <> show_type r b <> P.text ")"
show_type r (Meta i) = P.text "#" <> P.text (show i)
show_type r (RMeta a i) = P.text "#" <> P.text (show i) <> P.text "{^" <> P.text (show a) <> P.text "}"
show_type r (RField n p q) = P.text "{" <> P.text n <> P.text "¶ " <> show_type r p <> P.text "|" <> show_type r q <> P.text "}"
show_type r (RClosed) = P.text "{}"

instance Show a => Show (PType a) where
  show c = show (show_type 0 c)

syms :: Term -> S.Set Name
syms (Lam _ body) = syms body
syms (App f x) = syms f <> syms x
syms (Let _ arg body) = syms arg <> syms body
syms (Sym name) = S.singleton name
syms (Var _) = S.empty
syms (Lit _) = S.empty

instance ParseError SyntaxError where
  type EItem SyntaxError = Char
  endOfInput = EndOfInput
  unexpected = Unexpected
  noParse = NoParse

file :: Parser SyntaxError FileSyntax
file = do
  keyword "module"
  name <- identifier
  keyword "where"
  decls <- (sepBy decl (item ';') <* spaces <* eof) <|> (spaces *> pure [] <* eof)
  pure (name, decls)

decl :: Parser SyntaxError DeclarationSyntax
decl = definition

definition :: Parser SyntaxError DeclarationSyntax
definition = do
  name <- identifier
  args <- many identifier
  spaces *> item '='
  body <- expression (reverse args)
  pure $ Definition name (foldr Lam body args)

type Scope = [Name]

expression :: Scope -> Parser SyntaxError Term
expression r = lambda <|> letExpr <|> apply
  where lambda = do 
          spaces *> item 'λ'
          names <- some identifier
          spaces *> item '.'
          body <- expression (reverse names <> r)
          pure (foldr Lam body names)
        letExpr = keyword "let" *> letCont r
        letCont r = do
          name <- identifier
          spaces *> item '='
          arg <- expression r
          body <- (spaces *> item ';' *> letCont (name:r)) <|> letEnd (name:r)
          pure (Let name arg body)
        letEnd r = do
          keyword "in"
          body <- expression r
          pure body
        apply = do
          t <- term
          exprs <- many (lambda <|> letExpr <|> term)
          pure (foldl App t exprs)
        term = (spaces *> item '(' *> expression r <* spaces <* item ')')
           <|> num <|> ident
        num = do
          fmap (Lit . read) (spaces *> some (satisfy isDigit))
        ident = do
          name <- identifier
          case elemIndex name r of
            Just i -> pure (Var i)
            Nothing -> pure (Sym name)

identifier :: Parser SyntaxError String
identifier = perhaps notKw word
  where notKw p | p `elem` keywords = Left (ExpectedIdentifier p)
                | otherwise = Right p

keyword :: String -> Parser SyntaxError ()
keyword name = perhaps isKw word
  where isKw n | name == n = Right ()
               | otherwise = Left (ExpectedGot name n)

keywords :: [String]
keywords = ["let", "in", "module", "where"]

word :: Parser SyntaxError String
word = do
  spaces
  h <- satisfy isAlpha
  i <- many (satisfy isAlphaNum)
  pure (h:i)

spaces :: Parser SyntaxError [Char]
spaces = many (satisfy isSpace)
