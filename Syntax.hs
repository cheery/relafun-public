{-# LANGUAGE TypeFamilies, ImplicitParams, OverloadedStrings #-}
module Syntax where

import Control.Lens
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
import Wasm.Core
import Sub

data SyntaxError
  = EndOfInput
  | Unexpected Char
  | ExpectedIdentifier [Char]
  | ExpectedGot [Char] [Char]
  | NoParse
  deriving (Eq, Show)

type FileSyntax a = (String, ModuleContents)

data ModuleContents = ModuleContents {
  _definitions :: [(Name Tm, Tm)],
  _typeDecls   :: [(Name Tm, Ty)],
  _structDecls :: [(Name Ty, Bind [Name Ty] [(Name Tm, Ty)])],
  _instanceDecls :: [(Ty, Tm)],
  _typeAliases :: [(Name Ty, Bind [(Name Ty, Embed MKind)] (Maybe Ty))],
  _subFunctions :: [(Name Tm, SubFunction)],
  _subTypes :: [(String, SubType Inp)] }

emptyModule = ModuleContents [] [] [] [] [] [] []

-- bar :: Lens' (Foo a) Int
-- bar :: Functor f => (Int -> f Int) -> Foo a -> f (Foo a)
definitions f m = fmap (\a -> m {_definitions = a}) (f (_definitions m))
typeDecls f m = fmap (\a -> m {_typeDecls = a}) (f (_typeDecls m))
structDecls f m = fmap (\a -> m {_structDecls = a}) (f (_structDecls m))
instanceDecls f m = fmap (\a -> m {_instanceDecls = a}) (f (_instanceDecls m))
typeAliases f m = fmap (\a -> m {_typeAliases = a}) (f (_typeAliases m))
subFunctions f m = fmap (\a -> m {_subFunctions = a}) (f (_subFunctions m))
subTypes f m = fmap (\a -> m {_subTypes = a}) (f (_subTypes m))

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

type Readable a = Parser SyntaxError a
type DeclarationSyntax = ModuleContents -> ModuleContents

include lens item = over lens (item:)

file :: Parser SyntaxError (FileSyntax a)
file = do
  keyword "module"
  name <- identifier
  keyword "where"
  decls <- (sepBy decl (spaces *> item ';') <* spaces <* eof) <|> (spaces *> pure [] <* eof)
  pure (name, foldr ($) emptyModule decls)

decl :: Parser SyntaxError DeclarationSyntax
decl = definition <|> typedecl <|> structdecl <|> instancedecl
    <|> typealias <|> subfunction <|> subtype

typealias :: Readable DeclarationSyntax
typealias = do
  keyword "type"
  name <- identifier
  args <- many genericnamekind
  body <- pure Nothing <|> (symbol '=' *> (Just <$> generictype))
  pure $ include typeAliases (s2n name, bind args body)

subfunction :: Readable DeclarationSyntax
subfunction = do
  keyword "sub"
  symbols "function"
  name <- identifier
  symbol '('
  args <- sepBy argfield (symbol ',')
  symbol ')'
  restype <- (symbol ':' *> valtype) <|> pure (refn ANY) 
  symbol '{'
  body <- sepBy statement (symbol ';')
  symbol '}'
  pure $ include subFunctions (s2n name, (args, body, restype))
  where argfield = do
          doeval <- (symbols "noeval" *> pure False) <|> pure True
          (name,ty) <- nametype
          pure (doeval, name, ty)
        nametype = do
          name <- identifier
          symbol ':'
          ty <- valtype
          pure (name, ty)
        statement = storagestatement <|> returnstatement <|> dostatement
        storagestatement = do
          st <- sepBy1 nametype (symbol ',')
          symbol '='
          e <- expr
          pure (SubStore st e)
        returnstatement = symbols "return"
                       *> (SubReturn <$> sepBy expr (symbol ','))
        dostatement = SubDo <$> expr
        expr = exprAnn <|> exprPlus
        exprAnn = do
          tm <- exprPlus
          symbol ':'
          ty <- valtype
          pure (SubAnn tm ty)
        exprPlus = do
          tm <- exprApp
          tms <- many (symbol '+' *> exprApp)
          pure (foldl mkplus tm tms)
        mkplus a b = SubApp (SubApp (SubVar "+") a) b
        exprApp = do
          tm <- exprTerm
          tms <- many exprTerm
          pure (foldl SubApp tm tms)
        exprTerm = (symbol '(' *> expr <* symbol ')')
               <|> (SubVar <$> identifier)

subtype :: Readable DeclarationSyntax
subtype = do
  keyword "sub"
  keyword "type"
  name <- identifier
  symbol '='
  sub <- subtype
  pure $ include subTypes (name, sub)
  where subtype = fullsub <|> (Sub True [] <$> comptype)
        fullsub = do
          keyword "sub"
          final <- (symbols "final" *> pure True) <|> pure False
          symbol '('
          supers <- sepBy (Symbol <$> identifier) (symbol ',')
          symbol ')'
          ct <- comptype
          pure (Sub final supers ct)

valtype :: Readable (ValType Inp)
valtype = do
          head <- identifier
          case head of
            "i32" -> pure i32
            "i64" -> pure i64
            "f32" -> pure f32
            "f64" -> pure f64
            "v128" -> pure v128
            "ref" -> fromRefType <$> reftype
            _ -> empty
  where reftype = do
           nullable <- (symbols "null" *> pure True) <|> pure False   
           ht <- heaptype
           pure (Ref nullable ht)
        heaptype = (HT . Direct <$> comptype) <|> do
          head <- word
          case head of
            "any" -> pure ANY
            "eq" -> pure Wasm.Core.EQ
            "i31" -> pure I31
            "struct" -> pure STRUCT
            "array" -> pure ARRAY
            "none" -> pure NONE
            "func" -> pure FUNC
            "nofunc" -> pure NOFUNC
            "extern" -> pure EXTERN
            "noextern" -> pure NOEXTERN
            _ -> pure (HT (Symbol head))

comptype = array <|> struct <|> func
  where array = do
          symbols "array"
          ft <- fieldtype
          pure (Array ft)
        struct = do
          symbols "struct"
          symbol '{'
          fts <- sepBy fieldtype (symbol ';')
          symbol '}'
          pure (Struct fts)
        func = do
          symbols "func"
          symbol '('
          args <- sepBy valtype (symbol ',')
          symbol ')'
          res <- manyResult <|> oneResult <|> pure []
          pure (Func args res)
        fieldtype = do
          mut <- (symbols "imm" *> pure Imm)
             <|> (symbols "mut" *> pure Mut)
          st <- storagetype
          pure (st, mut)
        storagetype = (U <$> valtype) <|> packedtype
        packedtype = do
          head <- identifier
          case head of
            "i8" -> pure i8
            "i16" -> pure i16
            _ -> empty
        manyResult = do
          symbol '→'
          symbol '('
          results <- sepBy valtype (symbol ',')
          symbol ')'
          pure results
        oneResult = do
          symbol '→'
          pure <$> valtype

structdecl :: Parser SyntaxError DeclarationSyntax
structdecl = do
  keyword "struct"
  name <- identifier
  targs <- many (s2n <$> identifier)
  spaces *> item '{'
  labels <- sepBy labeldecl (spaces *> item ';')
  spaces *> item '}'
  pure $ include structDecls (s2n name, bind targs labels)
  where labeldecl = do
          label <- s2n <$> identifier
          spaces *> item ':'
          ty <- generictype
          pure (label, ty)

instancedecl :: Parser SyntaxError DeclarationSyntax
instancedecl = do
  keyword "instance"
  ty <- generictype
  spaces *> item '='
  tm <- expression
  pure $ include instanceDecls (ty, tm)

typedecl :: Parser SyntaxError DeclarationSyntax
typedecl = do
  name <- identifier
  spaces *> item ':'
  ty <- generictype
  pure $ include typeDecls (s2n name, ty)

generictype :: Parser SyntaxError Ty
generictype = fall <|> rule <|> typeExpr
  where fall = do
          spaces *> item '∀'
          namekinds <- some genericnamekind
          spaces *> item '.'
          ty <- rule <|> typeExpr
          pure (foldr mktall ty namekinds)
        mktall namekind ty = TAll (bind namekind ty)
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

genericnamekind = emb <$> (mrowkind <|> pkind <|> ((,MKind (KMeta holeMVar)) <$> s2n <$> identifier))
  where emb (x,y) = (x, Embed y)
        pkind = spaces *> item '(' *> (mrowkind <|> mkind) <* spaces <* item ')'
        mrowkind = (,) <$> (s2n <$> identifier)
                       <*> (MRow . sort <$> some (spaces *> item '^' *> identifier))
        mkind = (,) <$> (s2n <$> identifier) <*> (spaces *> item ':' *> (MKind <$> generickind))

generickind = kindArrow <|> kindTerm
  where kindArrow = (:->:) <$> kindTerm <*> (spaces *> item '→' *> generickind)
        kindTerm = kindTerm1 <|> kindTerm2
        kindTerm1 = (spaces *> item '(' *> generickind <* spaces <* item ')')
        kindTerm2 = do
          i <- word
          pure $ case i of
            "_" -> KMeta holeMVar
            "row" -> KRow
            "field" -> KField
            "type" -> KType

definition :: Parser SyntaxError DeclarationSyntax
definition = do
  name <- identifier
  args <- many (s2n <$> identifier)
  spaces *> item '='
  body <- expression
  pure $ include definitions (s2n name, foldr mklam body args)
  where mklam name body = Lam (bind name body)

expression :: Parser SyntaxError Tm
expression = lambda <|> letExpr <|> apply
  where lambda = do 
          spaces *> item 'λ'
          names <- some (s2n <$> identifier)
          spaces *> item '.'
          body <- expression
          pure (foldr mklam body names)
        mklam name body = Lam (bind name body)
        letExpr = keyword "let" *> letCont
        letCont = do
          name <- (pure Nothing <* spaces <* item '?')
              <|> (Just . s2n <$> identifier)
          spaces *> item '='
          arg <- expression
          body <- (spaces *> item ';' *> letCont) <|> letEnd
          case name of
            Nothing -> pure (ILet arg body)
            Just name -> pure (Let (bind (name, Embed arg) body))
        letEnd = do
          keyword "in"
          body <- expression
          pure body
        apply = do
          t <- termsuffix
          exprs <- many (lambda <|> letExpr <|> termsuffix)
          pure (foldl App t exprs)
        termsuffix = iapp <|> term
        iapp = do x <- term
                  spaces *> item '§'
                  f <- term
                  pure (App f x)
        term = (spaces *> item '(' *> expression <* spaces <* item ')')
           <|> num <|> ident <|> query <|> structure
        num = do
          fmap (Lit . read) (spaces *> some (satisfy isDigit))
        ident = do
          name <- identifier
          pure (Var (s2n name))
        query = spaces *> item '?' *> pure Query
        structure = do
          keyword "struct"
          spaces *> item '{'
          labels <- sepBy structfield (spaces *> item ';')
          spaces *> item '}'
          pure (TmStruct labels)
        structfield = do
          id <- identifier
          spaces *> item '='
          tm <- expression
          pure (id, tm)

identifier :: Parser SyntaxError String
identifier = perhaps notKw word
  where notKw p | p `elem` keywords = Left (ExpectedIdentifier p)
                | otherwise = Right p

keyword :: String -> Parser SyntaxError ()
keyword name = perhaps isKw word
  where isKw n | name == n = Right ()
               | otherwise = Left (ExpectedGot name n)

keywords :: [String]
keywords = ["let", "in", "module", "where", "absent", "present", "struct", "instance", "sub", "type"]

word :: Parser SyntaxError String
word = do
  spaces
  h <- satisfy isAlpha
  i <- many (satisfy (\a -> a == '_' || isAlphaNum a))
  pure (h:i)

symbols :: String -> Readable String
symbols s = (spaces *> items s)

symbol :: Char -> Readable Char
symbol s = (spaces *> item s)

spaces :: Parser SyntaxError [Char]
spaces = many (satisfy isSpace)
