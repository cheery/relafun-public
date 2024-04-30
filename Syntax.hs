{-# LANGUAGE TypeFamilies, ImplicitParams, OverloadedStrings #-}
module Syntax where

import Control.Applicative (Alternative (..))
import Data.Char
import Data.List (elemIndex, sort)
import qualified Data.Set as S
import Lib.Parser
import qualified Text.PrettyPrint as P
import Common
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Lib.Unify

data SyntaxError
  = EndOfInput
  | Unexpected Char
  | ExpectedIdentifier [Char]
  | ExpectedGot [Char] [Char]
  | NoParse
  deriving (Eq, Show)

type FileSyntax a = (String, [DeclarationSyntax a])

data DeclarationSyntax a
  = Definition String Tm
  | TypeDecl String Ty
  deriving (Show)

-- showType :: Int -> Ty -> P.Doc
-- showType r (TAll bnd) = "∀"
--   where (nk, ty) = coalesce bnd
--         coalesce bnd = let ((name, mkind), ty) = unsafeUnbind bnd
--                        in case ty of
--                                TAll bnd -> let (xs, ty) = coalesce bnd
--                                            in ((name, mkind):xs, ty)
--                                other -> ([], other)


--demo1 = quickParse generictype
--        "∀x y. x → y"
--demo2 = quickParse generictype
--        "∀x y^foo. {foo x | y}"

{--

outputType :: (Eq a, ?env :: [(a, String)]) => Int -> PType a Kind -> P.Doc
outputType r (Con _ "->" :$: [x,y])
  = parensLT (compare 0 r) $ outputType 1 x P.<+> "→" P.<+> outputType 0 y
outputType r (head :$: [])
  = outputTHead r head
outputType r (head :$: xs)
  = parensLT (compare 1 r) $ outputTHead 2 head P.<+> (P.nest 2 $ P.sep (map (outputType 2) xs))

outputTHead :: (Eq a, ?env :: [(a, String)]) => Int -> PHead a Kind -> P.Doc
outputTHead r (Con _ s) = P.text s
outputTHead r (Meta _ i) | Just s <- lookup i ?env = P.text s
outputTHead r x@(RMeta _ _) = "{" P.<> outputRow False [] x P.<> "}"
outputTHead r x@(RField _ _ _) = "{" P.<> outputRow False [] x P.<> "}"
outputTHead r RClosed = "{}"
outputTHead r FAbsent = "absent"
outputTHead r (FPresent xs) = parensLT (compare 1 r) $ "present" P.<+> (P.nest 2 $ P.sep (map (outputType 2) xs))

outputRow :: (Eq a, ?env :: [(a, String)]) => Bool -> [String] -> PHead a Kind -> P.Doc
outputRow com used (RMeta abs i) | Just s <- lookup i ?env
  = spaceTrue com $
    commaSep ["absent" P.<+> P.text a | a <- S.toList abs, not (elem a used)]
 P.<+> "| " P.<> P.text s
outputRow com used RClosed = P.empty
outputRow com used (RField name FAbsent next) = commaTrue com $
  "absent" P.<+> P.text name P.<> outputRow True (name:used) next
outputRow com used (RField name (FPresent xs) next) = commaTrue com $
  P.text name P.<+> P.sep (map (outputType 2) xs) P.<> outputRow True (name:used) next
outputRow com used (RField name p next) = commaTrue com $
  P.text name P.<> "?" P.<> outputTHead 2 p P.<> outputRow True (name:used) next

spaceTrue True p = " " P.<> p
spaceFalse False p = p

commaTrue True p = P.comma P.<+> p
commaTrue False p = p

commaSep [] = P.empty
commaSep [x] = x
commaSep (x:xs) = x P.<> P.comma P.<+> commaSep xs

parensLT LT = P.parens
parensLT _  = id
-- show_type :: Show a => Int -> PType a -> P.Doc
-- show_type r (Con s) = P.text s
-- show_type r (TApp (TApp (Con "->") a) b) = P.text "(" <> show_type r a <> P.text " -> " <> show_type r b <> P.text ")"
-- show_type r (TApp a b) = P.text "(" <> show_type r a <> P.text " " <> show_type r b <> P.text ")"
-- show_type r (Meta i) = P.text "#" <> P.text (show i)
-- show_type r (RMeta a i) = P.text "#" <> P.text (show i) <> P.text "{^" <> P.text (show a) <> P.text "}"
-- show_type r (RField n p q) = P.text "{" <> P.text n <> P.text "¶ " <> show_type r p <> P.text "|" <> show_type r q <> P.text "}"
-- show_type r (RClosed) = P.text "{}"
-- 
-- instance Show a => Show (PType a) where
--   show c = show (show_type 0 c)

--}

-- syms == fv' for now.

instance ParseError SyntaxError where
  type EItem SyntaxError = Char
  endOfInput = EndOfInput
  unexpected = Unexpected
  noParse = NoParse

file :: Parser SyntaxError (FileSyntax a)
file = do
  keyword "module"
  name <- identifier
  keyword "where"
  decls <- (sepBy decl (spaces *> item ';') <* spaces <* eof) <|> (spaces *> pure [] <* eof)
  pure (name, decls)

decl :: Parser SyntaxError (DeclarationSyntax a)
decl = definition <|> typedecl

typedecl :: Parser SyntaxError (DeclarationSyntax a)
typedecl = do
  name <- identifier
  spaces *> item ':'
  TypeDecl name <$> generictype

generictype :: Parser SyntaxError Ty
generictype = fall <|> rule <|> typeExpr
  where fall = do
          spaces *> item '∀'
          namekinds <- some (mrowkind <|> pkind <|> ((,MKind (KMeta holeMVar)) <$> s2n <$> identifier))

          spaces *> item '.'
          ty <- rule <|> typeExpr
          pure (foldr mktall ty namekinds)
        mktall (name, kind) ty = TAll (bind (name, Embed kind) ty)
        pkind = spaces *> item '(' *> (mrowkind <|> mkind) <* spaces <* item ')'
        mrowkind = (,) <$> (s2n <$> identifier)
                       <*> (MRow . sort <$> some (spaces *> item '^' *> identifier))
        mkind = (,) <$> (s2n <$> identifier) <*> (spaces *> item ':' *> (MKind <$> generickind))
        rule = do
          l <- typeExpr
          spaces *> item '⇒'
          r <- generictype
          pure (TRule l r)
        typeExpr = typeArrow <|> typeApp
        typeArrow = do
          l <- typeApp 
          spaces *> item '→'
          r <- typeExpr
          pure ((TVar (s2n "→") :$: l) :$: r)
        typeApp = do fs <- some typeTerm
                     let f = head fs
                     pure (foldl (:$:) f (tail fs))
        typeTerm = (spaces *> item '(' *> generictype <* spaces <* item ')')
               <|> typeIdentifier
               <|> typeAbsent
               <|> typePresent
               <|> typeParens
               <|> typeRow
        typeIdentifier = do i <- identifier
                            pure (TVar (s2n i))
        typeAbsent = keyword "absent" *> pure (TFAbsent)
        typePresent = do p <- (keyword "present" *> many typeTerm)
                         pure (TFPresent p)
        typeParens = spaces *> item '(' *> typeExpr <* spaces <* item ')'
        typeRow = do
          spaces *> item '{'
          e <- rowEntry <|> rowSuffix
          spaces *> item '}'
          pure e
        rowEntry = do (name, it) <- rowItem
                      TRField name it <$> ((spaces *> item ',' *> rowEntry) <|> rowSuffix)
        rowSuffix = (TVar . s2n <$> (spaces *> item '|' *> identifier))
                <|> (pure TREnd)
        rowItem = ((,TFAbsent) <$> (keyword "absent" *> identifier))
               <|> (,) <$> identifier <*> (spaces *> item '?' *> (TVar . s2n <$> identifier))
               <|> do n <- identifier
                      e <- many typeTerm
                      pure (n, TFPresent e)

generickind = kindArrow <|> kindTerm
  where kindArrow = (:->:) <$> kindTerm <*> (spaces *> item '→' *> generickind)
        kindTerm = kindTerm1 <|> kindTerm2
        kindTerm1 = (spaces *> item '(' *> generickind <* spaces <* item ')')
        kindTerm2 = do
          i <- identifier
          pure $ case i of
            "_" -> KMeta holeMVar
            "row" -> KRow
            "field" -> KField
            "type" -> KType

definition :: Parser SyntaxError (DeclarationSyntax a)
definition = do
  name <- identifier
  args <- many (s2n <$> identifier)
  spaces *> item '='
  body <- expression (reverse args)
  pure $ Definition name (foldr mklam body args)
  where mklam name body = Lam (bind name body)

type Scope = [Name Tm]

expression :: Scope -> Parser SyntaxError Tm
expression r = lambda <|> letExpr <|> apply
  where lambda = do 
          spaces *> item 'λ'
          names <- some (s2n <$> identifier)
          spaces *> item '.'
          body <- expression (reverse names <> r)
          pure (foldr mklam body names)
        mklam name body = Lam (bind name body)
        letExpr = keyword "let" *> letCont r
        letCont r = do
          name <- s2n <$> identifier
          spaces *> item '='
          arg <- expression r
          body <- (spaces *> item ';' *> letCont (name:r)) <|> letEnd (name:r)
          pure (Let (bind (name, Embed arg) body))
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
          pure (Var (s2n name))

identifier :: Parser SyntaxError String
identifier = perhaps notKw word
  where notKw p | p `elem` keywords = Left (ExpectedIdentifier p)
                | otherwise = Right p

keyword :: String -> Parser SyntaxError ()
keyword name = perhaps isKw word
  where isKw n | name == n = Right ()
               | otherwise = Left (ExpectedGot name n)

keywords :: [String]
keywords = ["let", "in", "module", "where", "absent", "present"]

word :: Parser SyntaxError String
word = do
  spaces
  h <- satisfy isAlpha
  i <- many (satisfy isAlphaNum)
  pure (h:i)

spaces :: Parser SyntaxError [Char]
spaces = many (satisfy isSpace)
