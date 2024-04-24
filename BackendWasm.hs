{-# LANGUAGE OverloadedStrings #-}
module BackendWasm where

import Wasm.Core hiding (Expr)
import qualified Wasm.CoreWriter as W
import qualified Wasm.CommonWriting as CW
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

compileFile :: FilePath -> [Bind] -> IO ()
compileFile p bd = CW.writeFile p
                                (compileDecls types (compile bd))

-- Compiler state handling.
data CompilerState = CompilerState {
  compilerLocals :: Locals,
  compilerFuncIdx :: [FuncIdx] }
type Locals = [ValType Inp]

initCS = CompilerState [] idxGen
idxGen = [0..]
nameGen = names 0 where names i = ("v" <> show i) : names (i+1)

reserveFuncIdx :: (State CompilerState :< eff) => Eff eff FuncIdx
reserveFuncIdx = do st <- get @CompilerState
                    let fix = compilerFuncIdx st
                    put @CompilerState $ st { compilerFuncIdx = tail fix }
                    pure (head fix)

setLocals :: (State CompilerState :< eff) => Locals -> Eff eff Locals
setLocals locals = do st <- get @CompilerState
                      put @CompilerState $ st { compilerLocals = locals }
                      pure (compilerLocals st)

reserveLocal :: (State CompilerState :< eff) => ValType Inp -> Eff eff LocalIdx
reserveLocal typ = do st <- get @CompilerState
                      put @CompilerState $ st { compilerLocals = compilerLocals st <> [typ] }
                      pure $ length (compilerLocals st)

type KernelMap = M.Map String FuncIdx

-- Actual compiler.
compile :: [Bind] -> [Declaration Inp]
compile bd = snd $ runEff' $ writeToList @(Declaration Inp)
           $ state @CompilerState initCS $ do
  write @(Declaration Inp)
        $ Import "kernel" "eval" (FuncImport (func [refn ANY] [refn ANY]))
  kernelEval <- reserveFuncIdx
  write @(Declaration Inp)
        $ Import "kernel" "apply" (FuncImport (func [refn ANY, ref "values"]
                                                    [refn ANY]))
  kernelApply <- reserveFuncIdx
  write @(Declaration Inp)
        $ Import "kernel" "begin-thunk" (FuncImport (func [ref "thunk"] [ref "values"]))
  kernelBeginThunk <- reserveFuncIdx
  write @(Declaration Inp)
        $ Import "kernel" "resolve" (FuncImport (func [refn ANY, ref "thunk"]
                                                      [refn ANY]))
  kernelResolve <- reserveFuncIdx
  write @(Declaration Inp)
        $ Import "kernel" "blackhole" (FuncImport "thunk-func")
  kernelBlackhole <- reserveFuncIdx
  let kernelMap = M.fromList [
                    ("eval", kernelEval),
                    ("apply", kernelApply),
                    ("begin-thunk", kernelBeginThunk),
                    ("resolve", kernelResolve),
                    ("blackhole", kernelBlackhole) ]
  -- The next line works because we don't export globals.
  let globals = M.fromList (zip (map fst bd) [0..])
      compileToplevelBind (name, obj)
        = do initializer <- compileObj globals kernelMap True [] obj
             write @(Declaration Inp)
                   $ Global (refn ANY) Imm initializer
             write @(Declaration Inp)
                   $ Export name (GlobalExport (globals M.! name))
  mapM_ compileToplevelBind bd

compileExpr :: (Write (Declaration Inp) :< eff,
               State CompilerState :< eff)
           => M.Map String Int -> KernelMap
           -> [(Int, AST Inp)] -> Expr -> Eff eff ([SCF Inp], AST Inp)
compileExpr glob kmap ctx (Atom a) = pure ([], compileAtom glob ctx a)
compileExpr glob kmap ctx (Apply f a)
  = do let res = I_Call (kmap M.! "apply") % [
                   I_Call (kmap M.! "eval") % [compileAtom glob ctx f],
                   I_ArrayNewFixed "values" (length a) % (map (compileAtom glob ctx) a)]
       pure ([], res)
compileExpr glob kmap ctx (Let bd e) = compileLet glob kmap ctx bd e
compileExpr glob kmap ctx (LetRec bd e) = do
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

compileLet :: (Write (Declaration Inp) :< eff,
               State CompilerState :< eff)
           => M.Map String Int -> KernelMap
           -> [(Int, AST Inp)] -> [Bind] -> Expr -> Eff eff ([SCF Inp], AST Inp)
compileLet glob kmap ctx [] e = compileExpr glob kmap ctx e
compileLet glob kmap ctx ((_,x):xs) e = do
  ref <- reserveLocal (refn ANY)
  let ctx' = (0, I_LocalGet ref % []) : map (\(i,e) -> (i+1, e)) ctx
  code <- compileObj glob kmap False ctx x
  (rest, res) <- compileLet glob kmap ctx' xs e
  pure ((Do (I_LocalSet ref % [code]):rest), res)
  
compileObj :: (Write (Declaration Inp) :< eff,
               State CompilerState :< eff)
           => M.Map String Int -> KernelMap
           -> Bool -> [(Int, AST Inp)] -> Obj -> Eff eff (AST Inp)
compileObj glob kmap toplevel ctx (Fun free n e) = do
  let arity = length n
      f i = case lookup i ctx of Just block -> block
      g i = I_ArrayGet "values" % [I_LocalGet 0 % [], I_I32Const (fromIntegral i) % []]
      h i = I_ArrayGet "values" % [I_LocalGet 1 % [], I_I32Const (fromIntegral i) % []]
      ctx' = zip free (map g [0..length free-1])
          <> zip [arity-1,arity-2..0] (map h [0..arity-1])
  uplocals <- setLocals [ref "values", ref "values"]
  (code, res) <- compileExpr glob kmap ctx' e
  locals <- setLocals uplocals
  funref <- reserveFuncIdx
  write @(Declaration Inp)
        $ ElemDeclareFunc funref
  write @(Declaration Inp)
        $ DefFunc "closure-func" (drop 2 locals)
                                 (code <> [Terminal (addReturn res)])
  pure (I_StructNew "closure" % [
          I_I32Const (fromIntegral arity) % [],
          I_ArrayNewFixed "values" (length free) % (map f free), 
          I_RefFunc funref % [] ])
compileObj glob kmap toplevel ctx (Pap f a) = do
  pure $ I_StructNew "pap" % [
           compileAtom glob ctx f,
           I_ArrayNewFixed "values" (length a) % (map (compileAtom glob ctx) a) ]
compileObj glob kmap toplevel ctx (Thunk free e) = do
  let f i = case lookup i ctx of Just block -> block
      g i = I_ArrayGet "values" % [I_LocalGet 1 % [], I_I32Const (fromIntegral i) % []]
      ctx' = zip free (map g [0..length free-1])
  uplocals <- setLocals [ref "thunk", ref "values"]
  (code, res) <- compileExpr glob kmap ctx' e
  locals <- setLocals uplocals
  funref <- reserveFuncIdx
  write @(Declaration Inp)
        $ ElemDeclareFunc funref
  if toplevel
  then write @(Declaration Inp)
             $ DefFunc "thunk-func" (drop 1 locals)
                                    (code <> [Terminal (addReturn res)])
  else write @(Declaration Inp)
             $ DefFunc "thunk-func" (drop 1 locals)
                                    ([Do $ I_LocalSet 1 % [I_Call (kmap M.! "begin-thunk") % [I_LocalGet 0 % []]]]
                                  <> code
                                  <> [Terminal (I_ReturnCall (kmap M.! "resolve") % [res, I_LocalGet 0 % []])])
  pure $ I_StructNew "thunk" % [I_RefFunc funref % [],
                                I_ArrayNewFixed "values" (length free) % (map f free)]

addReturn (Node (I_Call f) xs) = I_ReturnCall f % xs
addReturn node = I_Return % [node]

compileAtom :: M.Map String Int -> [(Int, AST Inp)] -> Atom -> AST Inp
compileAtom glob ctx (Var i) = case lookup i ctx of
                               Just block -> block
compileAtom glob ctx (Sym n) = I_GlobalGet (glob M.! n) % []
compileAtom glob ctx (Lit31i i) = I_RefI31 % [I_I32Const i % []]