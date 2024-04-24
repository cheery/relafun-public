{-# LANGUAGE OverloadedStrings, TypeFamilies #-}
module Sub where

import Lib.ContEff hiding (Context)
import Data.String (IsString(..))

-- For computing the SCC from typedecls, and for cfg graph manipulation.
import Lib.Graph (scc', preorder, buildG, sortedDomTree, rpnum, postorder, postorderF, dfs, transposeG, Tree(..))
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List (sort, elemIndex)
import Prelude hiding (EQ)
import Data.Maybe (fromJust)

-- For WAT output
import qualified Text.PrettyPrint as P

-- For control flow
import qualified Data.Array as A

class TypeOutput a where
  typeOutput :: a -> P.Doc

data NumType = I32 | I64 | F32 | F64
               deriving (Show, Eq, Ord)

instance TypeOutput NumType where
  typeOutput I32 = "i32"
  typeOutput I64 = "i64"
  typeOutput F32 = "f32"
  typeOutput F64 = "f64"

class IsNumType a where
  fromNumType :: NumType -> a
  i32, i64, f32, f64 :: a
  i32 = fromNumType I32
  i64 = fromNumType I64
  f32 = fromNumType F32
  f64 = fromNumType F64

instance IsNumType NumType where
  fromNumType = id

data PackedType = I8 | I16
               deriving (Show, Eq, Ord)

instance TypeOutput PackedType where
  typeOutput I8 = "i8"
  typeOutput I16 = "i16"

class IsPackedType a where
  fromPackedType :: PackedType -> a
  i8, i16 :: a
  i8 = fromPackedType I8
  i16 = fromPackedType I16

instance IsPackedType PackedType where
  fromPackedType = id

data VecType = V128
               deriving (Show, Eq, Ord)

instance TypeOutput VecType where
  typeOutput V128 = "v128"

class IsVecType a where
  fromVecType :: VecType -> a
  v128 :: a
  v128 = fromVecType V128

instance IsVecType VecType where
  fromVecType = id

data HeapType a = ANY | EQ | I31 | STRUCT | ARRAY
                | NONE | FUNC | NOFUNC | EXTERN | NOEXTERN
                | HT a
                deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Inp = TSym String
         | Direct (CompType Inp)
         deriving (Show)

instance IsCompType Inp where
  type Plug Inp = Inp
  fromCompType = Direct

data Can = Idx (Int, Int)
         | RecIdx Int
         deriving (Show, Eq, Ord)

instance TypeOutput (HeapType Int) where
  typeOutput ANY = "any"
  typeOutput EQ = "eq"
  typeOutput I31 = "i31"
  typeOutput STRUCT = "struct"
  typeOutput ARRAY = "array"
  typeOutput NONE = "none"
  typeOutput FUNC = "func"
  typeOutput NOFUNC = "nofunc"
  typeOutput EXTERN = "extern"
  typeOutput NOEXTERN = "noextern"
  typeOutput (HT i) = P.text (show i)

instance IsString Inp where
  fromString = TSym

instance IsString a => IsString (HeapType a) where
  fromString = HT . fromString

instance IsCompType (HeapType Inp) where
  type Plug (HeapType Inp) = Inp
  fromCompType = HT . Direct

data RefType a = Ref (HeapType a)
               | RefNull (HeapType a)
               deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance TypeOutput (RefType Int) where
  typeOutput (Ref p) = "(ref " P.<> typeOutput p P.<> ")"
  typeOutput (RefNull p) = "(ref null " P.<> typeOutput p P.<> ")"

class IsRefType f where
  fromRefType :: RefType a -> f a
  ref, refn :: HeapType a -> f a
  ref = fromRefType . Ref
  refn = fromRefType . RefNull

instance IsRefType RefType where
  fromRefType = id

data ValType a = N NumType
               | V VecType
               | R (RefType a)
               deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance TypeOutput (ValType Int) where
  typeOutput (N n) = typeOutput n
  typeOutput (V v) = typeOutput v
  typeOutput (R r) = typeOutput r

instance IsNumType (ValType a) where
  fromNumType = N

instance IsVecType (ValType a) where
  fromVecType = V

instance IsRefType ValType where
  fromRefType = R

data StorageType a = U (ValType a)
                   | P PackedType
                   deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance TypeOutput (StorageType Int) where
  typeOutput (U u) = typeOutput u
  typeOutput (P p) = typeOutput p

instance IsNumType (StorageType a) where
  fromNumType = U . fromNumType

instance IsVecType (StorageType a) where
  fromVecType = U . fromVecType

instance IsRefType StorageType where
  fromRefType = U . fromRefType

instance IsPackedType (StorageType a) where
  fromPackedType = P

data FieldType a = Imm (StorageType a)
                 | Mut (StorageType a)
                 deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance TypeOutput (FieldType Int) where
  typeOutput (Imm x) = typeOutput x
  typeOutput (Mut x) = "(mut " P.<> typeOutput x P.<> ")"

data CompType a = Array (FieldType a)
                | Struct [FieldType a]
                | Func [ValType a] [ValType a]
                deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance TypeOutput (CompType Int) where
  typeOutput (Array x) = "(array " P.<> typeOutput x P.<> ")"
  typeOutput (Struct xs) = "(struct " P.<> P.sep (map out xs) P.<> ")"
    where out x = "(field " P.<> typeOutput x P.<> ")"
  typeOutput (Func xs ys) = "(func " P.<> P.sep (map inp xs) P.<+> P.sep (map outp ys) P.<> ")"
    where inp x = "(param " P.<> typeOutput x P.<> ")"
          outp x = "(result " P.<> typeOutput x P.<> ")"

class IsCompType f where
  type Plug f
  fromCompType :: CompType (Plug f) -> f
  array  :: FieldType (Plug f) -> f
  array = fromCompType . Array
  struct :: [FieldType (Plug f)] -> f
  struct = fromCompType . Struct
  func   :: [ValType (Plug f)] -> [ValType (Plug f)] -> f
  func x y = fromCompType (Func x y)

instance IsCompType (CompType a) where
  type Plug (CompType a) = a
  fromCompType = id

-- On MVP, there can be only one supertype for now.
data SubType a = Sub  Final     (CompType a)
               | SubD Final a   (CompType a)
               deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
type Final = Bool

instance TypeOutput (SubType Int) where
  typeOutput (Sub True t) = typeOutput t
  typeOutput (Sub False t) = "(sub " P.<> typeOutput t P.<> ")"
  typeOutput (SubD True k t) = "(sub final " P.<> P.text (show k) P.<+> typeOutput t P.<> ")"
  typeOutput (SubD False k t) = "(sub " P.<> P.text (show k) P.<+> typeOutput t P.<> ")"

instance IsCompType (SubType a) where
  type Plug (SubType a) = a
  fromCompType c = Sub True c

type RecType a = [SubType a]

(?=) :: a -> Int -> (a, Int)
(?=) x y = (x, y)

(==>) :: b -> SubType a -> (b, SubType a)
(==>) x y = (x,y)

type TypeDecl = (String, SubType Inp)

recurse :: Traversable t
        => [String]
        -> M.Map String (Int, Int)
        -> [t Inp]
        -> ([t Can], [SubType Can]) 
recurse group m t = runEff'
                  $ writeToList @(SubType Can)
                  $ fmap snd
                  $ state @Int (length group)
                  $ traverse (traverse f) t
  where f (TSym sym) | Just i <- elemIndex sym group = pure $ RecIdx i
                     | otherwise = pure $ Idx (m M.! sym)
        f (Direct p) = do p' <- traverse f (Sub True p)
                          write @(SubType Can) p'
                          c <- get @Int
                          put @Int (c+1)
                          pure (RecIdx c)

-- Annotation step inserts recursion markers where needed
-- and groups everything into recursive groups.
annotateRec :: [TypeDecl] -> [[(String, SubType Inp)]]
annotateRec decls = map f (scctypes decls)
  where f group = [(name, subtype) | (name,subtype) <- g group ]
        g = map (\name -> (name, fromJust $ lookup name decls))
        k group a disc keep | Just a <- elemIndex a group = disc a
                            | otherwise = keep a

scctypes :: [TypeDecl] -> [[String]]
scctypes decls = map (map (dm M.!) . sort . preorder) (scc' graph)
  where graph = buildG (0, maximum (map fst defs)) edges
        edges = [(md M.! name, md M.! to) | (name,decl) <- decls, to <- foldr sfold [] decl, S.member to avail ]
        sfold (TSym s) ss = s:ss
        sfold (Direct p) ss = foldr sfold ss p
        dm     = M.fromList defs
        md     = M.fromList (invert defs)
        defs   = zip [0..] (map fst decls)
        invert = fmap (\(a,b) -> (b,a))
        avail  = S.fromList (map fst decls)

-- Canonicalization allows to determine equality between types.
-- use foldl canonicalize on annotateRec result.
-- typeOutputMap $ toTypemap $ fst $ foldl canonicalize (initCanon,initCanonMap) (annotateRec types)
type Canon = (M.Map Int [SubType Can],
              M.Map [SubType Can] Int,
              Int)
type CanonMap = M.Map String (Int,Int)

initCanon :: Canon
initCanon = (M.empty, M.empty, 0)

initCanonMap :: CanonMap
initCanonMap = M.empty

canonicalize :: (Canon, CanonMap) -> [(String, SubType Inp)] -> (Canon, CanonMap)
canonicalize ((p,q,c),m) group | Just i <- M.lookup sig q = ((p,q,c),
                                                             M.union m (M.fromList$zipWith (\name j -> (name, (i,j))) nams [0..]))
                               | otherwise = let p' = M.insert c sig p
                                                 q' = M.insert sig c q
                                                 c' = c + 1
                                                 m' = M.union m (M.fromList$zipWith (\name j -> (name, (c,j))) nams [0..])
                                             in ((p',q',c'), m')
  where sig = (\(x,y) -> x<>y) $ recurse (map fst group) m $ map snd group
        nams = map fst group

-- For handling anonymous type decls
-- TODO: This doesn't actually work like it should.
--       We are going to get rectypes instead of properly behaving separated types.
anoncanon :: (Canon, CanonMap) -> [SubType Inp] -> (Canon, Int)
anoncanon ((p,q,c), m) group | Just i <- M.lookup sig q = ((p,q,c), i)
                             | otherwise = let p' = M.insert c sig p
                                               q' = M.insert sig c q
                                               c' = c + 1
                                           in ((p',q',c'), c)
  where sig = (\(x,y) -> x<>y) $ recurse [] m $ group

-- TODO: since built on anoncanon, doesn't work like it should.
--       but works enough for simple stuff.
inpToTx :: Traversable t => (Canon, CanonMap) -> [t Inp] -> (Canon, [t TX])
inpToTx cx e = runEff' $ state @Canon (fst cx) $ mapM (mapM handle) e
  where handle (TSym sym) = pure (snd cx M.! sym)
        handle (Direct s) = do c <- get @Canon
                               let (c', i) = anoncanon (c, snd cx) [fromCompType s]
                               put @Canon c' 
                               pure (i, 0)

-- Build rec groups for building WAT output.
toTypemap :: Canon -> [[SubType Int]]
toTypemap canon@(m, _, _) = map f (M.toAscList m)
  where f (ind, group) = map (fmap (g ind)) group
        g ind (Idx i) = k M.! i
        g ind (RecIdx i) = k M.! (ind, i)
        k = toIndices canon

toTxTypeMap :: Canon -> M.Map TX (SubType TX)
toTxTypeMap canon@(m, _, _) = M.fromList [((i,j), fmap (g i) p)
                                         | (i, s) <- M.toAscList m, (p,j) <- zip s [0..]]
  where g ind (Idx i) = i
        g ind (RecIdx k) = (ind, k)

typeOutputMap :: [[SubType Int]] -> P.Doc
typeOutputMap ([g]:gs) = "(type" P.<+> typeOutput g P.<> ")"
                    P.$$ typeOutputMap gs
typeOutputMap (g:gs) = "(rec " P.<> P.sep (map typeOutput' g) P.<> ")"
                    P.$$ typeOutputMap gs
  where typeOutput' g = "(type" P.<+> typeOutput g P.<> ")"
typeOutputMap [] = ""

toIndices :: Canon -> M.Map (Int,Int) Int
toIndices (m, _, _) = M.fromList $ zip [(k,v) | (k,vs) <- M.toAscList m, v <- [0..length vs - 1]] [0..]

data Instruction t = Ins  String [Arg t]
                   | InsB String [Arg t] [Instruction t]
                   deriving (Show, Functor, Traversable, Foldable)
data Arg t = Typ (ValType t)
           | Val Int
           | ArgT t
           | ArgHeapType (HeapType t)
           | ArgResult (ValType t)
           deriving (Show, Functor, Traversable, Foldable)

instructionsOutput is = P.sep (map instructionOutput is)
instructionOutput (Ins name args) = P.text name P.<+> argsOutput args
instructionOutput (InsB name args is) = "(" P.<> P.text name
                                  P.$$ P.nest 2 (P.sep ([argsOutput args] <> map instructionOutput is)) P.<> ")"

argsOutput args = P.sep (map argOutput args)
argOutput (Typ t) = typeOutput t
argOutput (Val i) = P.text (show i)
argOutput (ArgT t) = P.text (show t)
argOutput (ArgHeapType t) = typeOutput t
argOutput (ArgResult t) = "(result" P.<+> typeOutput t P.<> ")"

data Cfg t = Cfg { entryLabel :: Label,
                   nodeBody :: [Action t],
                   flowLeaving :: ControlFlow t }
type Label = Int
data Action t
  = Store1 (Setter t) (ValType t)
  | Store [Setter t] (Expr t)
  | ArraySet (Expr t) (Expr t) (Expr t)
  | ArrayCopy (Expr t) (Expr t)
              (Expr t) (Expr t) (Expr t)
  | Unreachable
  deriving (Show, Functor, Traversable, Foldable)
data Setter t = Drop
              | GlobalSet Int
              | LocalSet Int
              deriving (Show, Functor, Traversable, Foldable)
data Expr t = LocalGet Int
            | GlobalGet Int
            | I32Const Integer
            | RefI31 (Expr t)
            | GetRefNull (RefType t)
            | GetRefFunc Int
            | StructNew (RefType t) [Expr t]
            | StructGet Int (Expr t)
            | ArrayNewFixed (RefType t) [Expr t]
            | ArrayNew (RefType t) (Expr t) (Expr t)
            | ArrayGet (Expr t) (Expr t)
            | ArrayLen (Expr t)
            | Call (Expr t) [Expr t]
            | CallI Int [Expr t]
            | RefCast (Expr t) (RefType t)
            | UpCast (Expr t) (RefType t)
  deriving (Show, Functor, Traversable, Foldable)

type TX = (Int,Int)
data TXContext = TXContext {
   txGlobals :: [ValType TX],
   txFunctions :: [TX],
   txTypeMap :: M.Map TX (SubType TX),
   txIndices :: M.Map TX Int }

txExpr :: TXContext -> [ValType TX]
       -> Bool
       -> Expr TX
       -> ([Instruction TX], [ValType TX])
txExpr tx locals retc (Call f xs) = (ii, outp)
  where (f', [t]) = txExpr tx locals False f
        xs' = map (txExpr tx locals False) xs
        --concat (map snd xs')
        R (Ref (HT rr)) = t
        Func inp outp = toCompType (txTypeMap tx M.! rr)
        ii = concat (map fst xs') <> f' <> [Ins name [ArgT rr]]
        name = if retc then "return_call_ref" else "call_ref"
txExpr tx locals retc (CallI f xs) = (ii, outp)
  where xs' = map (txExpr tx locals False) xs
        rr = txFunctions tx !! f
        --concat (map snd xs')
        Func inp outp = toCompType (txTypeMap tx M.! rr)
        ii = concat (map fst xs') <> [Ins name [Val f, ArgT rr]]
        name = if retc then "return_call" else "call"
txExpr tx locals True expr = (ii <> [Ins "return" []], [])
  where (ii,t) = txExpr tx locals False expr
txExpr tx locals False (LocalGet i) = ([Ins "local.get" [Val i]], [locals !! i])
txExpr tx locals False (GlobalGet i) = undefined
txExpr tx locals False (I32Const n) = undefined
txExpr tx locals False (RefI31 u) = undefined
txExpr tx locals False (GetRefNull t) = undefined
txExpr tx locals False (GetRefFunc i) = undefined
txExpr tx locals False (StructNew t es) = undefined
txExpr tx locals False (StructGet i e) = (ii, [toValType $ toStorageType r])
  where (e', [t]) = txExpr tx locals False e
        ii = e' <> [Ins "struct.get" [ArgHeapType t', Val i]]
        r  = rrr !! i
        Struct rrr = toCompType (txTypeMap tx M.! rr)
        R (Ref (HT rr)) = t
        R (Ref t') = t
txExpr tx locals False (ArrayNewFixed t es) = undefined
txExpr tx locals False (ArrayNew t a e) = undefined
txExpr tx locals False (ArrayGet e a) = undefined
txExpr tx locals False (RefCast e t) = undefined
txExpr tx locals False (UpCast e t) = undefined

toCompType (Sub _ c) = c
toCompType (SubD _ _ c) = c

toStorageType (Imm s) = s
toStorageType (Mut s) = s

toValType (U v) = v

txBlock :: TXContext -> [ValType TX]
       -> Action TX
       -> [Instruction TX]
txBlock tx locals act = case act of
  (Store1 setter typ) -> txSetter tx locals setter typ
  (Store setters expr) -> undefined
  (ArraySet expr idx val) -> undefined
  (ArrayCopy to tobase from frombase count) -> undefined
  Unreachable -> [Ins "unreachable" []]

txSetter :: TXContext -> [ValType TX]
         -> Setter TX
         -> ValType TX
         -> [Instruction TX]
txSetter tx locals setter vt = case setter of
  Drop -> [Ins "drop" []]
  LocalSet i -> [Ins "local.set" [Val i]]
  GlobalSet i -> [Ins "global.set" [Val i]]

data Control t
  = Do (Action t)
  | CastCase (Expr t) [(RefType t, Setter t, [Control t])]
                      (Maybe (RefType t, Setter t, [Control t]))
  | If (Expr t) [Control t] [Control t]
  | While (Expr t) [Control t]
  | Return (Maybe (Expr t))
  deriving (Show, Functor, Traversable, Foldable)

toCfg :: forall t. [Control t] -> [Cfg t]
toCfg block = map snd $ M.toAscList $ snd $ go initial block 0 [] Nothing
  where initial :: (Int, M.Map Int (Cfg t))
        initial = (1, M.empty)
        alloc (i,m) = ((i+1,m), i)
        intro (i,m) k b c = (i, M.insert k (Cfg k (reverse b) c) m)
        go st (Do p:cont) label rcode next =
          go st cont label (p:rcode) next
        go st1 (While c t:cont) label rcode next = let
            (st2,next') = alloc st1
            (st3,tb) = alloc st2
            (st4,bb) = alloc st3
            st5 = intro st4 label rcode (Unconditional tb)
            st6 = intro st5 tb [] (Conditional c bb next')
            st7 = go st6 t bb [] (Just tb)
          in go st7 cont next' [] next 
        go st1 (If e t f:cont) label rcode next = let
            (st2,next') = alloc st1
            (st3,tb) = alloc st2
            (st4,fb) = alloc st3
            st5 = go st4 t tb [] (Just next')
            st6 = go st5 f fb [] (Just next')
            st7 = intro st6 label rcode (Conditional e tb fb)
          in go st7 cont next' [] next 
        go st1 (CastCase e ss q:cont) label rcode next = let
            (st2,next') = alloc st1
            foldOne (typ, setter, block) st = let
              (st', this) = alloc st
              st'' = go st' (Do (Store1 setter (fromRefType typ)):block)
                             this [] (Just next')
              in (st'', Just this)
            folder (typ, setter, block) (st21,blks) = let
                (st22,this) = alloc st21
                st23 = go st22 (Do (Store1 setter (fromRefType typ)):block)
                             this [] (Just next')
              in (st23, ((typ,this):blks))
            (st3,blks) = foldr folder (st2,[]) ss
            (st4, q') = case q of
                          Nothing -> (st3, Nothing)
                          (Just qq) -> foldOne qq st3
            st5 = intro st4 label rcode (CastFlow e blks q')
          in go st5 cont next' [] next 
        go st (Return t:cont) label rcode next = 
          intro st label rcode (TerminalFlow t)
        go st [] label rcode Nothing =
          intro st label rcode (TerminalFlow Nothing)
        go st [] label rcode (Just next) =
          intro st label rcode (Unconditional next)

-- Aside control, we have declarations, which form the toplevel
-- of the module.
data Declaration t
  = ElemDeclareFunc Int
  | Global (ValType t) (Expr t)
  | DefFunc t [ValType t] [Control t]
  | ExportFunc String Int
  deriving (Show, Functor, Traversable, Foldable)

compileDecls :: [TypeDecl] -> [Declaration Inp] -> P.Doc
compileDecls types decls = "(module" P.<+> (P.nest 2 $ (typeOutputMap $ toTypemap canon')
                                                  P.$$ P.sep (map (declOutput tx) declsTX)) P.<> ")"
  where tx = TXContext {
              txGlobals = select getGlobalType declsTX,
              txFunctions = select getFuncType declsTX,
              txTypeMap = toTxTypeMap canon',
              txIndices = toIndices canon' }
        getGlobalType (Global t _) = Just t
        getGlobalType _ = Nothing
        getFuncType (DefFunc t _ _) = Just t
        getFuncType _ = Nothing
   --txTypeMap :: M.Map TX (SubType TX),
        (canon', declsTX) = inpToTx (canon, cmap) decls
        (canon, cmap) = foldl canonicalize (initCanon,initCanonMap) (annotateRec types)

declOutput :: TXContext -> Declaration TX -> P.Doc
declOutput tx (ElemDeclareFunc i)
  = "(elem declare func" P.<+> P.text (show i) P.<> ")"
declOutput tx (Global typ expr)
  = "(global" P.<+> typeOutput (xx typ)
  P.$$ P.nest 2 (instructionsOutput (map yy (fst $ txExpr tx [] False expr)))
  P.<> ")"
  where xx l = fmap (txIndices tx M.!) l
        yy l = fmap (txIndices tx M.!) l
declOutput tx (DefFunc typ locals ctl)
  = "(func (type" P.<+> P.text (show $ txIndices tx M.! typ) P.<> ")"
  P.<+> P.sep (map f locals)
  P.$$ P.nest 2 (instructionsOutput (map yy g)) P.<> ")"
  where f l = "(local" P.<+> typeOutput (xx l) P.<> ")"
        xx l = fmap (txIndices tx M.!) l
        yy l = fmap (txIndices tx M.!) l
        g = wasmCfg (structuredControl
                     (\b lab act -> txExpr tx locals' b act)
                     (\lab acts -> concat (map (txBlock tx locals') acts))
                     (toCfg ctl))
        (Sub True (Func inp outp)) = (txTypeMap tx M.! typ)
        locals' = inp <> locals
declOutput tx (ExportFunc name idx)
  = "(export \"" P.<> P.text name P.<> "\" (func"
  P.<+> P.text (show idx) P.<> "))"

data ControlFlow t
  = Unconditional Label
  | Conditional (Expr t) Label Label
  | CastFlow (Expr t) [(RefType t, Label)] (Maybe Label)
  | TerminalFlow (Maybe (Expr t))

cfgEdges :: Label -> ControlFlow t -> [(Label, Label)]
cfgEdges a (Unconditional label) = [(a,label)]
cfgEdges a (Conditional _ t f) = [(a,t), (a,f)]
cfgEdges a (CastFlow _ c m) = let tos = map snd c <> maybe [] pure m
                              in [(a,t) | t <- tos]
cfgEdges a (TerminalFlow _) = []

data Wasm t where
  WasmBlock   :: [Arg t] -> Wasm t -> Wasm t
  WasmLoop    :: Wasm t -> Wasm t
  WasmIf      :: [Instruction t] -> Wasm t -> Wasm t -> Wasm t
  WasmBr      :: Int -> Wasm t
  WasmActions :: [Instruction t] -> Wasm t
  WasmSeq     :: Wasm t -> Wasm t -> Wasm t

wasmCfg :: Wasm t -> [Instruction t]
wasmCfg (WasmBlock a b) = [InsB "block" a (wasmCfg b)]
wasmCfg (WasmLoop b) = [InsB "loop" [] (wasmCfg b)]
wasmCfg (WasmIf c t f) = c <> [InsB "if" [] [
                                 InsB "then" [] (wasmCfg t),
                                 InsB "else" [] (wasmCfg f)]]
wasmCfg (WasmBr i) = [Ins "br" [Val i]]
wasmCfg (WasmActions a) = a
wasmCfg (WasmSeq a b) = wasmCfg a <> wasmCfg b

deriving instance Show t => (Show (Wasm t))

instance Semigroup (Wasm t) where
  (<>) = WasmSeq

type Context = [ContainingSyntax]
data ContainingSyntax
  = IfThenElse
  | LoopHeadedBy Label
  | BlockFollowedBy Label

scDemo, scDemo2, scDemo3, scDemo4 :: Wasm Int
scDemo = structuredControl
         (\_ _ _ -> ([], [i32]))
         (\_ _ -> [])
         [Cfg 0 [] (TerminalFlow Nothing)]

scDemo2 = structuredControl
         (\_ _ _ -> ([], [i32]))
         (\_ _ -> [])
         [Cfg 0 [] $ Conditional (LocalGet 0) 1 2,
          Cfg 1 [] $ Unconditional 3,
          Cfg 2 [] $ Unconditional 3,
          Cfg 3 [] $ TerminalFlow Nothing]

scDemo3 = structuredControl
         (\_ _ _ -> ([], [i32]))
         (\_ _ -> [])
         [Cfg 0 [] $ CastFlow (LocalGet 0) [
                       (ref (HT 0), 1),
                       (ref (HT 1), 2) ] Nothing,
          Cfg 1 [] $ Unconditional 3,
          Cfg 2 [] $ Unconditional 3,
          Cfg 3 [] $ TerminalFlow Nothing]

-- instructionsOutput $ wasmCfg scDemo4
scDemo4 = structuredControl
          (\_ _ _ -> ([], [i32]))
          (\_ _ -> [])
          (toCfg ctlDemo)

ctlDemo :: [Control Int]
ctlDemo = [
  If (LocalGet 0) [] [] ]

structuredControl
  :: forall t.
     (Bool -> Label -> Expr t -> ([Instruction t], [ValType t]))
  -> (Label -> [Action t] -> [Instruction t])
  -> [Cfg t]
  -> Wasm t
structuredControl txExpr txBlock graph = doTree domTree []
  where domTree = fmap (blockmap M.!) (sortedDomTree g 0)
        g = buildG (0, length graph)
                   [edge | cfg <- graph,
                           edge <- cfgEdges (entryLabel cfg) (flowLeaving cfg)]
        q = transposeG g
        blockmap = M.fromList [(entryLabel cfg, cfg) | cfg <- graph]
        doTree :: Tree (Cfg t) -> Context -> Wasm t
        doTree (Node x children) context =
          let codeForX = nodeWithin x (filter hasMergeRoot children)
          in if isLoopHeader x then
               WasmLoop (codeForX (LoopHeadedBy (entryLabel x) : context))
             else
               codeForX context
          where hasMergeRoot = isMergeNode . rootLabel
        
        nodeWithin :: Cfg t -> [Tree (Cfg t)] -> Context -> Wasm t
        nodeWithin x (y_n:ys) context
           = WasmBlock [] (nodeWithin x ys (BlockFollowedBy ylabel : context))
          <> doTree y_n context
          where ylabel = entryLabel (rootLabel y_n)
        nodeWithin x [] context
           = WasmActions (txBlock xlabel (nodeBody x))
          <> case flowLeaving x of
               Unconditional l -> doBranch xlabel l context
               Conditional e t f ->
                 WasmIf (fst $ txExpr False xlabel e)
                        (doBranch xlabel t (IfThenElse : context))
                        (doBranch xlabel f (IfThenElse : context))
               CastFlow e brc m ->
                 let doCastFlow [] cx
                       = let (code, [typ]) = txExpr False xlabel e
                       in WasmSeq (WasmActions code)
                        $ WasmSeq (WasmActions [
                                   Ins "br_on_cast" [
                                       Val (index t cx),
                                       Typ typ,
                                       Typ (fromRefType k)] | (k,t) <- brc])
                                 (case m of
                                   Nothing -> WasmActions [Ins "unreachable" []]
                                   Just t -> doBranch xlabel t cx)
                     doCastFlow ((k,t):bc) cx
                       = WasmSeq (WasmBlock [ArgResult (fromRefType k)]
                                            (doCastFlow bc (BlockFollowedBy t:cx)))
                                 (doBranch xlabel t cx)
                                   
                 in doCastFlow brc context
               TerminalFlow Nothing -> WasmActions [Ins "return" []]
               TerminalFlow (Just e) -> WasmActions (fst $ txExpr True xlabel e)
          where xlabel = entryLabel x
        
        doBranch :: Label -> Label -> Context -> Wasm t
        doBranch source target context
          | isBackward source target = WasmBr i
          | isMergeLabel target      = WasmBr i
          | otherwise = doTree (subtreeAt target) context
          where i = index target context

        rp = rpnum g 0
        isBackward :: Label -> Label -> Bool
        isBackward from to = rp M.! to <= rp M.! from
        
        isMergeLabel :: Label -> Bool
        isMergeLabel l = S.member l mergeBlockLabels
        isMergeNode = isMergeLabel . entryLabel

        mergeBlockLabels :: S.Set Label
        mergeBlockLabels = S.fromList [entryLabel n | n <- rpblocks,
                                       length (forwardPreds (entryLabel n)) >= 2]

        forwardPreds to = [from | from <- q A.! to, not (isBackward from to)]
        
        rpblocks :: [Cfg t]
        rpblocks = map (blockmap M.!) (reverse (postorderF (dfs g [0])))

        rootLabel :: Tree (Cfg t) -> Cfg t
        rootLabel (Node root _) = root
        
        subtreeAt label = subtrees M.! label
        subtrees :: M.Map Label (Tree (Cfg t))
        subtrees = addSubtree M.empty domTree
          where addSubtree map t@(Node root children) =
                  foldl addSubtree (M.insert (entryLabel root) t map) children

        isLoopHeader = isHeaderLabel . entryLabel
        isHeaderLabel = (`S.member` headers)
          where headers :: S.Set Label
                headers = foldMap headersPointedTo blockmap
                headersPointedTo block =
                  S.fromList [label | label <- g A.! entryLabel block,
                                               dominates label (entryLabel block)]

        dominates label blockname =
          label == blockname || elem blockname (map entryLabel (postorder (subtreeAt label)))

index :: Label -> Context -> Int
index label (frame : context)
  | matchesFrame label frame = 0
  | otherwise                = 1 + index label context
  where matchesFrame label (BlockFollowedBy l) = (label == l)
        matchesFrame label (LoopHeadedBy l)    = (label == l)
        matchesFrame _ _ = False

-- TODO: Should go to utils
-- mapMaybe
select :: (a -> Maybe b) -> [a] -> [b]
select f [] = []
select f (x:xs) | Just y <- f x = y : select f xs
                | otherwise     = select f xs
