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

type FileSyntax a = (String, Module)

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
  pure (name, bind [] (foldr ($) emptyModule decls))

decl :: Parser SyntaxError DeclarationSyntax
decl = definition <|> typedecl <|> structdecl <|> instancedecl
    <|> typealias <|> subfunction <|> subtype

typealias :: Readable DeclarationSyntax
typealias = do
  keyword "type"
  name <- identifier
  args <- many genericnamekind
  body <- pure Nothing <|> (symbol '=' *> (Just <$> generictype []))
  let kind = foldr (:->:) KType (map (getKind.unembed.snd) args)
  let manifest = case body of
                    Nothing -> Abstract
                    Just body -> Alias (bind args body)
  pure $ include (specification.typeSigs) (s2n name, kind, manifest)

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
  pure $ include values (s2n name, ValueSubFunction . ignore $ (args, body, restype))
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
  pure $ include (specification.subTypeSigs) (name, ignore sub)
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
  targs <- many genericnamekind
  spaces *> item '{'
  labels <- sepBy labeldecl (spaces *> item ';')
  spaces *> item '}'
  let kind = foldr (:->:) KType (map (getKind.unembed.snd) targs)
  let manifest = StructDecl (bind targs labels)
  pure $ include (specification.typeSigs) (s2n name, kind, manifest)
  where labeldecl = do
          label <- s2n <$> identifier
          spaces *> item ':'
          ty <- generictype []
          pure (label, ty)

instancedecl :: Parser SyntaxError DeclarationSyntax
instancedecl = do
  keyword "instance"
  name <- s2n <$> identifier
  symbol ':'
  ty <- generictype []
  pure $ include (specification.valueSigs) (True, name, ty)

typedecl :: Parser SyntaxError DeclarationSyntax
typedecl = do
  name <- identifier
  spaces *> item ':'
  ty <- generictype []
  pure $ include (specification.valueSigs) (False, s2n name, ty)

generictype :: [Name Ty] -> Parser SyntaxError Ty
generictype env = fall <|> rule <|> typeExpr
  where fall = do
          spaces *> item '∀'
          namekinds <- some genericnamekind
          spaces *> item '.'
          ty <- generictype (map fst namekinds <> env)
          pure (foldr mktall ty namekinds)
        mktall namekind ty = TAll (bind namekind ty)
        rule = do
          l <- typeExpr
          spaces *> item '⇒'
          r <- generictype env
          pure (TRule l r)
        typeExpr = typeArrow <|> typeApp
        typeArrow = do
          l <- typeApp 
          symbol '→'
          r <- typeExpr
          pure ((TIdent (PId $ s2n "→") :$: l) :$: r)
        typeApp = do fs <- some typeTerm
                     let f = head fs
                     pure (foldl (:$:) f (tail fs))
        typeTerm = (spaces *> item '(' *> generictype env <* spaces <* item ')')
               <|> typeIdentifier
               <|> typeAbsent
               <|> typePresent
               <|> typeParens
               <|> typeRow
        typeIdentifier
          = do name <- identifier
               if elem (s2n name) env
               then pure (TVar (s2n name))
               else pure (TIdent (PId (s2n name)))
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
  body <- expression []
  pure $ include values (s2n name, Value $ foldr mklam body args)
  where mklam name body = Lam (bind name body)

expression :: [Name Tm] -> Parser SyntaxError Tm
expression env = lambda <|> letExpr <|> apply
  where lambda = do 
          spaces *> item 'λ'
          names <- some (s2n <$> identifier)
          spaces *> item '.'
          body <- expression (names <> env)
          pure (foldr mklam body names)
        mklam name body = Lam (bind name body)
        letExpr = keyword "let" *> letCont env
        letCont env = do
          name <- (pure Nothing <* spaces <* item '?')
              <|> (Just . s2n <$> identifier)
          spaces *> item '='
          arg <- expression env
          let env' = (maybe env (:env) name)
          body <- (spaces *> item ';' *> letCont env') <|> letEnd env'
          case name of
            Nothing -> pure (ILet arg body)
            Just name -> pure (Let (bind (name, Embed arg) body))
        letEnd env = do
          keyword "in"
          body <- expression env
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
        term = (spaces *> item '(' *> expression env <* spaces <* item ')')
           <|> num <|> ident <|> query <|> structure
        num = do
          fmap (Lit . read) (spaces *> some (satisfy isDigit))
        ident = do
          name <- identifier
          if elem (s2n name) env
          then pure (Var (s2n name))
          else pure (Ident (PId (s2n name)))
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
          tm <- expression env
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
