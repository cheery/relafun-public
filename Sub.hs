{-# LANGUAGE OverloadedStrings, TypeFamilies, GADTs #-}
module Sub where

import Control.Lens hiding (index, Context)
import Data.Proxy
import Data.Maybe (mapMaybe)
import Lib.ContEff hiding (Context)
import Data.String (IsString(..))
import Wasm.Core

-- For computing the SCC from typedecls, and for cfg graph manipulation.
import Lib.Graph (scc', preorder, buildG, sortedDomTree, rpnum, postorder, postorderF, dfs, transposeG, Tree(..))
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List (sort, elemIndex)
import Prelude hiding (EQ)
import Data.Maybe (fromJust)

-- For control flow
import qualified Data.Array as A

-- Debugging aid
(!?) :: (Ord a, Show a) => M.Map a b -> a -> b
(!?) m a | Just b <- M.lookup a m = b
         | otherwise = error $ "key " <> show a <> " not present"

data Inp = Symbol String
         | Direct (CompType Inp)
         deriving (Show)

instance IsCompType Inp where
  type Plug Inp = Inp
  fromCompType = Direct

instance IsString Inp where
  fromString = Symbol
 
-- Canonicalization
data Can = Idx TX
         | RecIdx Int
         deriving (Show, Eq, Ord)
type TX = (Int, Int)


-- Type declaration form-up
type TypeDecl = (String, SubType Inp)

(==>) :: b -> SubType a -> (b, SubType a)
(==>) x y = (x,y)

-- For notating instruction trees.
(%) :: a -> [Tree a] -> Tree a
(%) = Node

tDemo :: Tree (Instruction Int)
tDemo = I_Return % [I_LocalGet 0 % []]

-- Annotation step inserts recursion markers where needed
-- and groups everything into recursive groups.
annotateRec :: [TypeDecl] -> [[TypeDecl]]
annotateRec decls = map f (scctypes decls)
  where f group = [(name, subtype) | (name,subtype) <- g group ]
        g = map (\name -> (name, fromJust $ lookup name decls))
        k group a disc keep | Just a <- elemIndex a group = disc a
                            | otherwise = keep a

scctypes :: [TypeDecl] -> [[String]]
scctypes decls = map (map (dm !?) . sort . preorder) (scc' graph)
  where graph = buildG (0, maximum (map fst defs)) edges
        edges = [(md !? name, md !? to)
                | (name, Sub _ r ct) <- decls,
                  to <- foldr sfold (foldr sfold [] r) ct, S.member to avail ]
        sfold :: Inp -> [String] -> [String]
        sfold (Symbol s) ss = s:ss
        sfold (Direct p) ss = foldr sfold ss p
        dm     = M.fromList defs
        md     = M.fromList (invert defs)
        defs   = zip [0..] (map fst decls)
        invert = fmap (\(a,b) -> (b,a))
        avail  = S.fromList (map fst decls)

-- Canonicalization allows to detect equality between types.
isRecursive :: Foldable t => [String] -> t Inp -> Bool
isRecursive g = foldl go False
  where go p (Symbol t) = p || t `elem` g
        go p (Direct t) = foldl go p t

data CanonState = CanonState {
  mapToCanon :: M.Map Int [SubType Can],
  mapFromCanon :: M.Map [SubType Can] Int,
  mapNameToTX  :: M.Map String TX,
  nextRecGroup :: Int,
  nextLocalId  :: Int }

initCanon :: CanonState
initCanon = CanonState M.empty M.empty M.empty 0 0

canonicalize :: (State CanonState :< eff)
             => [TypeDecl] -> Eff eff ()
canonicalize group = do i <- install (map fst group) (map snd group)
                        mapM_ (register i) (zip (map fst group) [0..])
  where register :: (State CanonState :< eff) => Int -> (String, Int) -> Eff eff ()
        register i (n,j) = do st <- get @CanonState
                              let m = M.insert n (i,j) (mapNameToTX st)
                              put @CanonState $ st { mapNameToTX = m }

getcanon :: (State CanonState :< eff)
         => Inp -> Eff eff (Int, Int)
getcanon (Symbol s) = do st <- get @CanonState
                         pure (mapNameToTX st !? s)
getcanon (Direct ct) = do i <- install [] [fromCompType ct]
                          pure (i,0)

install :: (State CanonState :< eff)
        => [String] -> [SubType Inp] -> Eff eff Int
install names group = do sig <- inpToCan names group
                         st <- get @CanonState
                         case M.lookup sig (mapFromCanon st) of
                           Just i -> pure i
                           Nothing -> do let p = M.insert (nextRecGroup st) sig (mapToCanon st)
                                             q = M.insert sig (nextRecGroup st) (mapFromCanon st)
                                             c = nextRecGroup st + 1
                                         put @CanonState $ st { mapToCanon = p,
                                                                mapFromCanon = q,
                                                                nextRecGroup = c }
                                         pure (nextRecGroup st)

inpToCan :: (State CanonState :< eff)
         => [String] -> [SubType Inp] -> Eff eff [SubType Can]
inpToCan names group = do st <- get @CanonState
                          put @CanonState $ st { nextLocalId = length group }
                          (a,b) <- writeToList @(SubType Can) (mapM (mapM go) group)
                          pure (a <> b)
  where go (Direct ct) | isRecursive names ct = do ct' <- mapM go ct
                                                   write @(SubType Can) (fromCompType ct')
                                                   st <- get @CanonState
                                                   put @CanonState $ st { nextLocalId = nextLocalId st + 1 }
                                                   pure (RecIdx (nextLocalId st))
        go (Symbol s) | Just i <- elemIndex s names = pure (RecIdx i)
        go inp = Idx <$> getcanon inp

-- Build rec groups for building WASM output.
toTypeSection :: CanonState -> [RecType Int]
toTypeSection st = map f (M.toAscList (mapToCanon st))
  where f (ind, group) = map (fmap (g ind)) group
        g ind (Idx i) = k !? i
        g ind (RecIdx i) = k !? (ind, i)
        k = toIndices st

toIndices :: CanonState -> M.Map TX Int
toIndices st = M.fromList $ zip [(k,v)
                                 | (k,vs) <- M.toAscList (mapToCanon st),
                                   v <- [0..length vs - 1]] [0..]

-- typeMap is for type checking.
toTypeMap :: CanonState -> M.Map Int (SubType Int)
toTypeMap st = M.fromList [(ix M.! (i,j), fmap (g i) p)
                          | (i, s) <- M.toAscList (mapToCanon st),
                              (p,j) <- zip s [0..]]
  where g ind (Idx i) = ix M.! i
        g ind (RecIdx k) = ix M.! (ind, k)
        ix = toIndices st

-- Structured control flow
data SCF t
  = Do (AST t)
  | CastCase (AST t) (RefType t) [(RefType t, [SCF t])] (Maybe [SCF t])
  | If (AST t) [SCF t] [SCF t]
  | While (AST t) [SCF t]
  | Terminal (AST t)
  deriving (Show, Functor, Traversable, Foldable)

toCfg :: forall t. [SCF t] -> [Cfg t]
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
         go st1 (CastCase e t ss q:cont) label rcode next = let
             (st2,next') = alloc st1
             foldOne block st = let
               (st', this) = alloc st
               st'' = go st' block this [] (Just next')
               in (st'', Just this)
             folder (typ, block) (st21,blks) = let
                 (st22,this) = alloc st21
                 st23 = go st22 block this [] (Just next')
               in (st23, ((typ,this):blks))
             (st3,blks) = foldr folder (st2,[]) ss
             (st4, q') = case q of
                           Nothing -> (st3, Nothing)
                           (Just qq) -> foldOne qq st3
             st5 = intro st4 label rcode (CastFlow e t blks q')
           in go st5 cont next' [] next 
         go st (Terminal t:cont) label rcode next = 
           intro st label (t:rcode) TerminalFlow
         go st [] label rcode Nothing =
           intro st label rcode TerminalFlow
         go st [] label rcode (Just next) =
           intro st label rcode (Unconditional next)

-- Control flow graphs
type AST t = Tree (Instruction t)
data Cfg t = Cfg { entryLabel :: Label,
                   nodeBody :: [AST t],
                   flowLeaving :: ControlFlow t }
             deriving (Show)
type Label = Int

data ControlFlow t
  = Unconditional Label
  | Conditional (AST t) Label Label
  | CastFlow (AST t) (RefType t) [(RefType t, Label)] (Maybe Label)
  | TerminalFlow
  deriving (Show)

cfgEdges :: Label -> ControlFlow t -> [(Label, Label)]
cfgEdges a (Unconditional label) = [(a,label)]
cfgEdges a (Conditional _ t f) = [(a,t), (a,f)]
cfgEdges a (CastFlow _ _ c m) = let tos = map snd c <> maybe [] pure m
                                in [(a,t) | t <- tos]
cfgEdges a TerminalFlow = []

data Wasm t where
  WasmBlock   :: BlockType t -> Wasm t -> Wasm t
  WasmLoop    :: Wasm t -> Wasm t
  WasmIf      :: [Instruction t] -> Wasm t -> Wasm t -> Wasm t
  WasmBr      :: Int -> Wasm t
  WasmActions :: [Instruction t] -> Wasm t
  WasmSeq     :: Wasm t -> Wasm t -> Wasm t

wasmCfg :: Wasm t -> [Instruction t]
wasmCfg (WasmBlock a b) = [I_Block a (wasmCfg b)]
wasmCfg (WasmLoop b) = [I_Loop BNone (wasmCfg b)]
wasmCfg (WasmIf c t f) = c <> [I_IfElse BNone (wasmCfg t) (wasmCfg f)]
wasmCfg (WasmBr i) = [I_Br i]
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

structuredControl :: forall t. [Cfg t] -> Wasm t
structuredControl graph = doTree domTree []
  where domTree = fmap (blockmap !?) (sortedDomTree g 0)
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
           = WasmBlock BNone (nodeWithin x ys (BlockFollowedBy ylabel : context))
          <> doTree y_n context
          where ylabel = entryLabel (rootLabel y_n)
        nodeWithin x [] context
           = WasmActions (concat (map postorder (nodeBody x)))
          <> case flowLeaving x of
               Unconditional l -> doBranch xlabel l context
               Conditional e t f ->
                 WasmIf (postorder e)
                        (doBranch xlabel t (IfThenElse : context))
                        (doBranch xlabel f (IfThenElse : context))
                 <> WasmActions [I_Unreachable]
               CastFlow e (Ref frb typ) brc m ->
                 let doCastFlow [] cx
                        = WasmSeq (WasmActions (postorder e))
                        $ WasmSeq (WasmActions [
                                   I_BrOnCast (frb, trb)
                                              (index t cx)
                                              typ
                                              k | (Ref trb k,t) <- brc])
                                 (case m of
                                   Nothing -> WasmActions [I_Unreachable]
                                   Just t -> doBranch xlabel t cx)
                     doCastFlow ((k,t):bc) cx
                       = WasmSeq (WasmBlock (BVal (fromRefType k))
                                            (doCastFlow bc (BlockFollowedBy t:cx)))
                                 (doBranch xlabel t cx)
                                   
                 in doCastFlow brc context
               TerminalFlow -> WasmActions []
          where xlabel = entryLabel x
        
        doBranch :: Label -> Label -> Context -> Wasm t
        doBranch source target context
          | isBackward source target = WasmBr i
          | isMergeLabel target      = WasmBr i
          | otherwise = doTree (subtreeAt target) context
          where i = index target context

        rp = rpnum g 0
        isBackward :: Label -> Label -> Bool
        isBackward from to = rp !? to <= rp !? from
        
        isMergeLabel :: Label -> Bool
        isMergeLabel l = S.member l mergeBlockLabels
        isMergeNode = isMergeLabel . entryLabel

        mergeBlockLabels :: S.Set Label
        mergeBlockLabels = S.fromList [entryLabel n | n <- rpblocks,
                                       length (forwardPreds (entryLabel n)) >= 2]

        forwardPreds to = [from | from <- q A.! to, not (isBackward from to)]
        
        rpblocks :: [Cfg t]
        rpblocks = map (blockmap !?) (reverse (postorderF (dfs g [0])))

        rootLabel :: Tree (Cfg t) -> Cfg t
        rootLabel (Node root _) = root
        
        subtreeAt label = subtrees !? label
        subtrees :: M.Map Label (Tree (Cfg t))
        subtrees = addSubtree M.empty domTree
          where addSubtree map t@(Node root children) =
                  foldl addSubtree (M.insert (entryLabel root) t map) children

        isLoopHeader = isHeaderLabel . entryLabel
        isHeaderLabel = (`S.member` headers)
          where headers :: S.Set Label
                headers = foldMap headersPointedTo (postorder domTree)
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

type SubFunction = ([(Bool, String, ValType Inp)], [SubBlock Inp], ValType Inp)
data SubBlock t = SubDo (SubTm t)
                | SubStore [(String, ValType t)] (SubTm t)
                | SubReturn [SubTm t]
                deriving (Show, Functor, Traversable, Foldable)
data SubTm t = SubVar String
             | SubApp (SubTm t) (SubTm t)
             | SubAnn (SubTm t) (ValType t)
             deriving (Show, Functor, Traversable, Foldable)

data Output a = Output {
  _typeSection :: [RecType a],
  _importSection :: [(String, String, ImportDesc a)],
  _functionSection :: [a],
  _globalSection :: [((ValType a, Mut), (Expr a))],
  _exportSection :: [(String, ExportDesc)],
  _elementSection :: [Elem],
  _codeSection :: [([ValType a], Expr a)] }
  deriving (Show, Functor, Traversable, Foldable)

emptyOutput = Output [] [] [] [] [] [] []

typeSection f m = fmap (\a -> m {_typeSection = a}) (f (_typeSection m))
importSection f m = fmap (\a -> m {_importSection = a}) (f (_importSection m))
functionSection f m = fmap (\a -> m {_functionSection = a}) (f (_functionSection m))
globalSection f m = fmap (\a -> m {_globalSection = a}) (f (_globalSection m))
exportSection f m = fmap (\a -> m {_exportSection = a}) (f (_exportSection m))
elementSection f m = fmap (\a -> m {_elementSection = a}) (f (_elementSection m))
codeSection f m = fmap (\a -> m {_codeSection = a}) (f (_codeSection m))

-- For easier insertion.
push :: forall a b eff. (State a :< eff)
     => Lens' a [b] -> b -> Eff eff ()
push lens item = modify @a (over lens (item:))

data SubState f = SubState {
  _subCanon :: CanonState,
  _subOutput :: Output Int,
  _subTypeMap :: M.Map Int (SubType Int),
  _subNameMap :: M.Map String Int,
  _subExtra :: f }

subCanon f m = fmap (\a -> m {_subCanon = a}) (f (_subCanon m))
subOutput f m = fmap (\a -> m {_subOutput = a}) (f (_subOutput m))
subTypeMap f m = fmap (\a -> m {_subTypeMap = a}) (f (_subTypeMap m))
subNameMap f m = fmap (\a -> m {_subNameMap = a}) (f (_subNameMap m))
subExtra f m = fmap (\a -> m {_subExtra = a}) (f (_subExtra m))

-- Some push helpers where needed.
global vt m e = ((vt, m), postorder e)
elemDeclareFunc f = (Elem3 ElemKindRefFunc [f])
code labels body = (labels, wasmCfg (structuredControl (toCfg body)))

compileDecls typedecls output extra envelope subStage = do
  (canon, (output', envelope')) <- state initCanon $ do
    mapM_ canonicalize (annotateRec typedecls)
    output' <- mapM getcanon output
    envelope' <- mapM getcanon envelope
    pure (output', envelope')
  let indices = toIndices canon
      nameMap = fmap (indices M.!) (mapNameToTX canon)
      output'' = fmap (indices M.!) output'
      envelope'' = fmap (indices M.!) envelope'
      subState = SubState {
        _subCanon = canon,
        _subOutput = over typeSection
                          (reverse (toTypeSection canon) <>)
                          output'' ,
        _subTypeMap = toTypeMap canon,
        _subNameMap = nameMap,
        _subExtra = extra }
  (subState', ()) <- state subState (subStage envelope'')
  pure (outputCore (subState'^.subOutput))

outputCore :: Output Int -> Core
outputCore output = section TypeSection (output^.typeSection)
                  . section ImportSection (output^.importSection)
                  . section FunctionSection (output^.functionSection)
                  . section GlobalSection (output^.globalSection)
                  . section ExportSection (output^.exportSection)
                  . section ElementSection (output^.elementSection)
                  . section CodeSection (output^.codeSection) $ []
  where section sec [] = id
        section sec xs = (sec (reverse xs):)

-- This happens in awkward location.
data SubEnv a = SubEnv [(String, ValType a)]

subInference :: forall a. (Ord a, Show a)
             => (M.Map String Int)
             -> M.Map a (SubType a)
             -> M.Map String a
             -> M.Map String Int
             -> [(Bool, String, ValType a)]
             -> [SubBlock a]
             -> ValType a
             -> ([ValType a], [SCF a])
subInference globals txmap txname kernelMap args body restype
  = refine $ runEff' $ state (SubEnv nargs) $ ((intro <>) . concat <$> mapM inferBlock body)
  where refine (SubEnv l, scf) = (map snd l, scf)
        nargs = [(name, ty) | (_, name, ty) <- args]
        intro = [
          Do (I_LocalSet (i+2) % [
            let getter = I_ArrayGet (txname M.! "values") % [I_LocalGet 1 % [], I_I32Const (fromIntegral i) % []]
                refcast (R (Ref null ht)) ast = I_RefCast null ht % [ast]
            in if ev then refcast ty (I_Call (kernelMap M.! "eval") % [ getter ])
                     else refcast ty getter])
          | (i, (ev, name, ty)) <- zip [0..] args ]
        inferBlock (SubDo tm) = do (ast, typs) <- infer tm
                                   pure $ [Do ast] <> map (\_ -> Do $ I_Drop % []) typs
        inferBlock (SubStore storg tm) = do ix <- mapM deflocal storg
                                            ast <- check tm (map snd storg)
                                            pure $ [Do ast] 
                                                <> [Do (I_LocalSet (i+2) % [])
                                                   | i <- reverse ix]
        inferBlock (SubReturn [tm]) = do ast <- check tm [restype]
                                         pure [Terminal $ doreturn $ ast]
        -- TODO: return call optimization.
        doreturn t = I_Return % [t]
        deflocal (name,ty) = do SubEnv locals <- get @(SubEnv a)
                                let locals' = case lookup name locals of
                                                Nothing -> locals <> [(name, ty)]
                                                Just _ -> locals
                                put @(SubEnv a) (SubEnv locals')
                                case elemIndex (name,ty) locals' of
                                  Nothing -> error "local type mismatch"
                                  Just ix -> pure ix
        infer (SubAnn tm ty) = do ast <- check tm [ty]
                                  pure (ast, [ty])
        infer tm = do let head = funroll tm
                          args = fargs tm
                      inferable head args
        check tm restypes = do let head = funroll tm
                                   args = fargs tm
                               checkable head args restypes
        funroll (SubVar s) = s
        funroll (SubApp f _) = funroll f
        fargs tm = fargs' tm []
        fargs' (SubVar _) a = a
        fargs' (SubApp f x) a = fargs' f (x:a)
        inferable "get_s" [arg] = do (ast, tys) <- infer arg
                                     case tys of
                                       [R (Ref _ I31)] -> pure (I_I31GetS % [ast], [i32])
                                       tys -> error $ "get_s on " <> show tys
        inferable name [] = do SubEnv locals <- get @(SubEnv a)
                               case lookup name locals of
                                 Just ty -> case elemIndex (name,ty) locals of
                                                 Just ix -> pure (I_LocalGet (ix+2) % [], [ty])
                                 Nothing -> case M.lookup name globals of
                                                 Just ix -> pure (I_GlobalGet ix % [], [refn ANY])
                                                 Nothing -> error $ "unknown constant " <> name
        inferable "i31" [arg] = do ast <- check arg [i32]
                                   pure (I_RefI31 % [ast], [ref I31])
        inferable "+" [a, b] = do (ast1, ty1) <- infer a
                                  (ast2, ty2) <- infer b
                                  if ty1 == ty2 && ty1 == [i32]
                                  then pure (I_I32Add % [ast1, ast2], [i32])
                                  else error "type error"
        inferable name _ = error name
        checkable "new" args [R (Ref _ (HT i))]
          | Just (Sub _ _ (Struct fields)) <- M.lookup i txmap
          , length args == length fields
          = do asts <- sequence (zipWith (\(ts,_) tm -> check tm [unpack ts]) fields args)
               pure (I_StructNew i % asts)
        checkable name args tys' = do (ast,tys) <- inferable name args
                                      if tys' == tys
                                      then pure ast
                                      else error $ "type error at " <> name
        unpack (U ty) = ty
        unpack (P _)  = i32
