{-# LANGUAGE OverloadedStrings #-}
module BackendWasm where

import Control.Lens
import Data.Kind (Type)
import Data.Proxy
import Unbound.Generics.LocallyNameless
import Lib.UnboundEff (Fresh', freshEff)
import Wasm.Core hiding (Expr)
import qualified Wasm.CoreWriter as W
import qualified Wasm.CommonWriting as CW
import qualified Common as C
import Sub
import SubKernel (types)
import Lib.Graph (Tree(..))

import Lib.ContEff
import Backend
import Data.String (IsString(..))
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Text.PrettyPrint as P
import Control.Monad.Fail


-- Hack for handling some specials we got in this code.
instance MonadFail (Eff eff) where
  fail = undefined

compileFile :: FilePath
            -> [TypeDecl]
            -> [(Bool, Name Atom, Embed Obj)]
            -> [(Name Atom, SubFunction)]
            -> IO ()
compileFile p localtypes bd subfunctions
  = CW.writeFile p (compile (types <> localtypes)
                            bd subfunctions)

-- Compiler state handling.
data CompilerState = CompilerState {
  _compilerLocals :: Locals,
  _compilerFuncIdx :: [FuncIdx],
  _compilerFuncMap :: KernelMap,
  _compilerGlobalIdx :: [GlobalIdx],
  _compilerGlobals :: M.Map String GlobalIdx }
type Locals = [ValType Inp]
type KernelMap = M.Map String FuncIdx

compilerLocals f m = fmap (\a -> m {_compilerLocals = a}) (f (_compilerLocals m))
compilerFuncIdx f m = fmap (\a -> m {_compilerFuncIdx = a}) (f (_compilerFuncIdx m))
compilerFuncMap f m = fmap (\a -> m {_compilerFuncMap = a}) (f (_compilerFuncMap m))
compilerGlobalIdx f m = fmap (\a -> m {_compilerGlobalIdx = a}) (f (_compilerGlobalIdx m))
compilerGlobals f m = fmap (\a -> m {_compilerGlobals = a}) (f (_compilerGlobals m))

initCS = CompilerState [] idxGen M.empty idxGen M.empty
idxGen = [0..]

-- Reserve is generic for handling idxGen items
reserve :: forall a b eff. (State a :< eff) => Lens' a [b] -> Eff eff b
reserve lens = do i <- (^.(lens . to head)) <$> get @a
                  modify @a $ over lens tail
                  pure i

update :: forall a b c eff. (Ord b, State a :< eff)
       => Lens' a (M.Map b c) -> b -> c -> Eff eff ()
update lens n v = modify @a (over lens (M.insert n v))

teeLocals :: forall a eff. (State a :< eff) => Lens' a Locals -> Locals -> Eff eff Locals
teeLocals lens locals = do l <- (^.lens) <$> get @a
                           modify @a $ set lens locals
                           pure l

allocLocal :: forall a eff. (State a :< eff) => Lens' a Locals -> ValType Inp -> Eff eff LocalIdx
allocLocal lens typ = do len <- (^.(lens.to length)) <$> get @a
                         modify @a $ over lens (<> [typ])
                         pure len

type FullState = (CompilerState, Output Inp)
compilerState :: Lens' FullState CompilerState
compilerState = _1
outputState :: Lens' FullState (Output Inp)
outputState = _2

pushdeffunc :: (State FullState :< eff)
            => Inp -> [ValType Inp] -> [SCF Inp] -> Eff eff ()
pushdeffunc ty locals body = do
  push (outputState.functionSection) ty
  push (outputState.codeSection)
       (code locals body)

data Envelope t = Envelope [(Name Atom, ([(Bool, String, ValType t)],
                                         [SubBlock t],
                                         ValType t))]
                deriving (Functor, Traversable, Foldable)


compile :: [TypeDecl]
        -> [(Bool, Name Atom, Embed Obj)]
        -> [(Name Atom, SubFunction)]
        -> Core
compile typedecls bd subfunctions
  = snd $ runEff' $ freshEff $ state (initCS, emptyOutput :: Output Inp)
  $ do let imp n m t = do
             push (outputState.importSection) (n, m, FuncImport t)
             reserve (compilerState.compilerFuncIdx)
               >>= update (compilerState.compilerFuncMap) m
       imp "kernel" "eval" (func [refn ANY] [refn ANY] :: Inp)
       imp "kernel" "apply" (func [refn ANY, ref "values"] [refn ANY])
       imp "kernel" "begin-thunk" (func [ref "thunk"] [ref "values"])
       imp "kernel" "resolve" (func [refn ANY, ref "thunk"] [refn ANY])
       imp "kernel" "blackhole" "thunk-func"
       -- Do global reservation beforehand
       -- This works as long as we don't declare new globals
       -- in middle of the compiling, which we don't.
       let resv n = do g <- reserve (compilerState.compilerGlobalIdx)
                       update (compilerState.compilerGlobals) n g
       mapM_ (\(_,n,_) -> resv (name2String n)) bd
       mapM_ (\(n,_) -> resv (name2String n)) subfunctions
       let pushglobal ty imm init
             = do push (outputState.globalSection)
                       (global ty imm init)
           pushexportglobal name
             = do globals <- (^.(compilerState.compilerGlobals)) <$> get
                  let idx = (globals M.! name)
                  push (outputState.exportSection) (name, GlobalExport idx)
           compileToplevelBind (exp, name, Embed obj)
             = do initializer <- compileObj True [] obj
                  pushglobal (refn ANY) Imm initializer
                  if exp
                  then pushexportglobal (name2String name)
                  else pure ()
       mapM_ compileToplevelBind bd
       st <- get @FullState
       let compileSubFunctions (Envelope subfunctions)
             = mapM_ compileSubFunction subfunctions
           compileSubFunction (name, (args, body, restype))
             = do let name' = name2String name
                  funref <- reserve (subExtra.compilerFuncIdx)
                  nameMap <- (^.subNameMap) <$> get @(SubState CompilerState)
                  let initializer = (I_StructNew (nameMap M.! "closure") % [
                        I_I32Const (fromIntegral (length args)) % [],
                        I_ArrayNewFixed (nameMap M.! "values") 0 % [], 
                        I_RefFunc funref % [] ])
                  push @(SubState CompilerState)
                       (subOutput.globalSection)
                       (global (refn ANY) Imm initializer)
                  st <- get @(SubState CompilerState)
                  let (locals, body') = subInference
                        (st^.subExtra.compilerGlobals)
                        (st^.subTypeMap)
                        (st^.subNameMap)
                        (st^.subExtra.compilerFuncMap)
                        args
                        body
                        restype
                  push @(SubState CompilerState)
                       (subOutput.functionSection) (nameMap M.! "closure-func")
                  push @(SubState CompilerState)
                       (subOutput.codeSection)
                       (code locals body')
                  globals <- (^.(subExtra.compilerGlobals)) <$> get
                  let idx = (globals M.! name')
                  push @(SubState CompilerState)
                       (subOutput.exportSection) (name', GlobalExport idx)
       compileDecls typedecls (st^.outputState)
                              (st^.compilerState)
                              (Envelope subfunctions)
                              (compileSubFunctions)
          
compileExpr :: (Fresh' :< eff, State FullState :< eff)
           => [(Name Atom, AST Inp)] -> Expr -> Eff eff ([SCF Inp], AST Inp)
compileExpr ctx (Atom a) = do glob <- (^.(compilerState.compilerGlobals)) <$> get
                              pure ([], compileAtom glob ctx a)
compileExpr ctx (Apply f a)
  = do glob <- (^.(compilerState.compilerGlobals)) <$> get
       kmap <- (^.(compilerState.compilerFuncMap)) <$> get
       let res = I_Call (kmap M.! "apply") % [
                   I_Call (kmap M.! "eval") % [compileAtom glob ctx f],
                   I_ArrayNewFixed "values" (length a) % (map (compileAtom glob ctx) a)]
       pure ([], res)
compileExpr ctx (Let bnd) = do
  (bd, e) <- unbind bnd
  compileLet ctx [bd] e
{--
compileExpr ctx (LetRec bd e) = do
  let count = length bd
  locals <- mapM (\_ -> reserveLocal (refn ANY)) bd
  let ctx' = [(i, I_LocalGet ref % []) | (i, ref) <- zip [count-1,count-2..0] locals]
          <> map (\(i,e) -> (i+count, e)) ctx
  -- allocate thunk for each local
  let g local = Do $ I_LocalSet local % [
                       I_StructNew "thunk" % [
                         I_RefFunc (kmap M.! "blackhole") % [],
                         I_RefNull ANY % [] ] ]
      top = map g locals
  -- generate code for each thunk set.
  let f (local, (_, y)) = do code <- compileObj glob kmap False ctx' y
                             pure $ Do $ I_Drop % [
                                           I_Call (kmap M.! "resolve") % [
                                             code,
                                             I_LocalGet local % [] ]]
  prefix <- mapM f (zip locals bd)
  (code, res) <- compileExpr glob kmap ctx' e
  pure (top <> prefix <> code, res)
--}

compileLet :: (Fresh' :< eff, State FullState :< eff)
           => [(Name Atom, AST Inp)] -> [(Name Atom, Embed Obj)] -> Expr -> Eff eff ([SCF Inp], AST Inp)
compileLet ctx [] e = compileExpr ctx e
compileLet ctx ((name,Embed x):xs) e = do
  ref <- allocLocal (compilerState.compilerLocals) (refn ANY)
  let ctx' = (name, I_LocalGet ref % []) : ctx
  code <- compileObj False ctx x
  (rest, res) <- compileLet ctx' xs e
  pure ((Do (I_LocalSet ref % [code]):rest), res)
  
compileObj :: (Fresh' :< eff, State FullState :< eff)
           => Bool -> [(Name Atom, AST Inp)] -> Obj -> Eff eff (AST Inp)
compileObj toplevel ctx (Fun free bnd) = do
  (n, e) <- unbind bnd
  let arity = length n
      f i = case lookup i ctx of Just block -> block
      g i = I_ArrayGet "values" % [I_LocalGet 0 % [], I_I32Const (fromIntegral i) % []]
      h i = I_ArrayGet "values" % [I_LocalGet 1 % [], I_I32Const (fromIntegral i) % []]
      ctx' = zip free (map g [0..length free-1])
          <> zip n (map h [0..arity-1])
  uplocals <- teeLocals (compilerState.compilerLocals) [ref "values", ref "values"]
  (code, res) <- compileExpr ctx' e
  locals <- teeLocals (compilerState.compilerLocals) uplocals
  funref <- reserve (compilerState.compilerFuncIdx)
  push (outputState.elementSection) (elemDeclareFunc funref)
  pushdeffunc "closure-func" (drop 2 locals)
                             (code <> [Terminal (addReturn res)])
  pure (I_StructNew "closure" % [
          I_I32Const (fromIntegral arity) % [],
          I_ArrayNewFixed "values" (length free) % (map f free), 
          I_RefFunc funref % [] ])
compileObj toplevel ctx (Pap f a) = do
  glob <- (^.(compilerState.compilerGlobals)) <$> get
  pure $ I_StructNew "pap" % [
           compileAtom glob ctx f,
           I_ArrayNewFixed "values" (length a) % (map (compileAtom glob ctx) a) ]
compileObj toplevel ctx (Thunk free e) = do
  kmap <- (^.(compilerState.compilerFuncMap)) <$> get
  let f i = case lookup i ctx of Just block -> block
      g i = I_ArrayGet "values" % [I_LocalGet 1 % [], I_I32Const (fromIntegral i) % []]
      ctx' = zip free (map g [0..length free-1])
  uplocals <- teeLocals (compilerState.compilerLocals) [ref "thunk", ref "values"]
  (code, res) <- compileExpr ctx' e
  locals <- teeLocals (compilerState.compilerLocals) uplocals
  funref <- reserve (compilerState.compilerFuncIdx)
  push (outputState.elementSection) (elemDeclareFunc funref)
  if toplevel
  then pushdeffunc "thunk-func" (drop 1 locals)
                                (code <> [Terminal (addReturn res)])
  else pushdeffunc "thunk-func" (drop 1 locals)
                                ([Do $ I_LocalSet 1 % [I_Call (kmap M.! "begin-thunk") % [I_LocalGet 0 % []]]]
                                  <> code
                                  <> [Terminal (I_ReturnCall (kmap M.! "resolve") % [res, I_LocalGet 0 % []])])
  pure $ I_StructNew "thunk" % [I_RefFunc funref % [],
                                I_ArrayNewFixed "values" (length free) % (map f free)]

addReturn (Node (I_Call f) xs) = I_ReturnCall f % xs
addReturn node = I_Return % [node]

compileAtom :: M.Map String Int -> [(Name Atom, AST Inp)] -> Atom -> AST Inp
compileAtom glob ctx (Var i) = case lookup i ctx of
                               Just block -> block
                               Nothing    -> case M.lookup (name2String i) glob of
                                   Just idx -> I_GlobalGet idx % []
                                   Nothing -> error $ "name missing: " <> show glob <> " " <> show ctx <> " " <> show i
compileAtom glob ctx (Lit31i i) = I_RefI31 % [I_I32Const i % []]
--}
