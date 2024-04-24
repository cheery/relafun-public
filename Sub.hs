{-# LANGUAGE OverloadedStrings, TypeFamilies #-}
module Sub where

import Data.Maybe (mapMaybe)
import Lib.ContEff hiding (Context)
import Data.String (IsString(..))
import Wasm.Core hiding (Expr)

-- For computing the SCC from typedecls, and for cfg graph manipulation.
import Lib.Graph (scc', preorder, buildG, sortedDomTree, rpnum, postorder, postorderF, dfs, transposeG, Tree(..))
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List (sort, elemIndex)
import Prelude hiding (EQ)
import Data.Maybe (fromJust)

-- For control flow
import qualified Data.Array as A

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
scctypes decls = map (map (dm M.!) . sort . preorder) (scc' graph)
  where graph = buildG (0, maximum (map fst defs)) edges
        edges = [(md M.! name, md M.! to)
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
                         pure (mapNameToTX st M.! s)
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
        g ind (Idx i) = k M.! i
        g ind (RecIdx i) = k M.! (ind, i)
        k = toIndices st

toIndices :: CanonState -> M.Map TX Int
toIndices st = M.fromList $ zip [(k,v)
                                 | (k,vs) <- M.toAscList (mapToCanon st),
                                   v <- [0..length vs - 1]] [0..]

-- txTypeMap is for type checking.
toTxTypeMap :: CanonState -> M.Map TX (SubType TX)
toTxTypeMap st = M.fromList [((i,j), fmap (g i) p)
                            | (i, s) <- M.toAscList (mapToCanon st),
                              (p,j) <- zip s [0..]]
  where g ind (Idx i) = i
        g ind (RecIdx k) = (ind, k)

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
type Label = Int

data ControlFlow t
  = Unconditional Label
  | Conditional (AST t) Label Label
  | CastFlow (AST t) (RefType t) [(RefType t, Label)] (Maybe Label)
  | TerminalFlow

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

-- Declarations, which form the toplevel of the module.
data Declaration t
  = ElemDeclareFunc Int
  | Global (ValType t) Mut (AST t)
  | DefFunc t [ValType t] [SCF t]
  | Export String ExportDesc
  | Import String String (ImportDesc t)
  deriving (Show, Functor, Traversable, Foldable)

compileDecls :: [TypeDecl] -> [Declaration Inp] -> Core
compileDecls td d = section TypeSection types
                  . section ImportSection imports
                  . section FunctionSection funcTypes
                  . section GlobalSection globals
                  . section ExportSection exports
                  . section ElementSection elements
                  . section CodeSection codes $ []
  where section sec xs | length xs > 0 = (sec xs:)
                       | otherwise     = id
        types = toTypeSection canon
        imports = mapMaybe getImport d'
        getImport (Import n m i) = Just (n,m,i)
        getImport _ = Nothing
        funcTypes = mapMaybe getFuncType d'
        getFuncType (DefFunc t _ _) = Just t
        getFuncType _ = Nothing
        globals = mapMaybe getGlobal d'
        getGlobal (Global vt m e) = Just ((vt,m), postorder e)
        getGlobal _ = Nothing
        exports = mapMaybe getExport d'
        getExport (Export name desc) = Just (name,desc)
        getExport _ = Nothing
        elements = mapMaybe getElement d'
        getElement (ElemDeclareFunc f) = Just (Elem3 ElemKindRefFunc [f])
        getElement _ = Nothing
        codes = mapMaybe getCode d'
        getCode (DefFunc _ l e) = Just (l, wasmCfg (structuredControl (toCfg e)))
        getCode _ = Nothing
        (canon,d') = runEff' $ state initCanon $ do
          mapM_ canonicalize (annotateRec td)
          d' <- mapM (mapM getcanon) d
          indices <- toIndices <$> get @CanonState
          pure $ map (fmap (indices M.!)) d'
