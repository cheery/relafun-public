{-# LANGUAGE DataKinds, ImplicitParams, OverloadedStrings #-}
module Compiler where

import Data.Maybe (mapMaybe)
import Lib.ContEff
import Control.Monad (foldM)
import Data.Maybe (fromJust)
import Lib.Parser (quickParse)
import Syntax
import Lib.Graph (scc', preorder, buildG)
import Inference
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Backend as B
import qualified BackendWasm as BW
import qualified ToBackend as TB
import qualified Text.PrettyPrint as P
import System.Exit
import System.Environment

main = do
  args <- getArgs
  entry (args !! 0) (args !! 1)

entry inf outf = do
  text <- readFile inf
  case quickParse file text of
    Left err -> print err
    Right (name, decls) -> do
      let blocks = sccBlocks (mapMaybe (defOnly syms) decls)
      let ((tp,prog), err) = snd $ runEff'
                    $ runUnify @Type initUnify
                    $ writeToList @(Name, InferenceError)
                    $ proceed blocks decls
      if length err /= 0
      then do print err
              exitWith (ExitFailure 0)
      else do let g = map (\(x,y) -> (x, TB.toObj [] y)) prog
              mapM_ printTypeScheme (M.toList tp)
              mapM_ print prog
              mapM_ print g
              BW.compileFile outf g

printTypeScheme (name, TypeScheme _ env tp cs)
 = let ?env = env in
   let prefix = if length env == 0
                then P.empty
                else "∀" P.<> P.sep (map (P.text . snd) env) P.<> "."
       prefix2 = if S.size cs == 0
                then P.empty
                else commaSep [P.text name P.<+> outputType 0 t
                              | CSi name t <- S.toList cs]
   in print (P.text name P.<+> ":" P.<+> prefix P.<+> prefix2 P.<+> outputType 0 tp)

proceed blocks decls = do
  foldM (declBlock decls) (M.empty :: M.Map String TypeScheme,
                           []) blocks

declBlock :: (Unify Type :< eff, Write (Name, InferenceError) :< eff)
          => [DeclarationSyntax MVar]
          -> (M.Map String TypeScheme, [(String, Term)])
          -> [Name]
          -> Eff eff (M.Map String TypeScheme, [(String, Term)])
declBlock decls (types, prog) block = do
  let terms = filter (\(name,_) -> name `elem` block)
            $ mapMaybe (defOnly id) decls
  let perTerm (name, term)
        = do (typing, errs) <- writeToList @InferenceError
                   $ infer types [] term >>= reify
             mapM (\err -> write (name, err)) errs
             let Typing _ t c = typing
             let vs = free t <> M.unions (map free (S.toList c))
             pure (name, TypeScheme vs (nameThemAbc $ M.keys vs) t c, term)
  schemes <- mapM perTerm terms

  pure (types <> M.fromList (map (\(x,y,_) -> (x,y)) schemes),
        prog <> map (\(x,_,z) -> (x,z)) schemes)

sccBlocks :: [(Name, S.Set Name)] -> [[Name]]
sccBlocks defs = map (map (defMapF M.!) . preorder) (scc' graph)
  where graph     = buildG (0,maximum (map fst defMap)) edges
        edges     = [(defMapI M.! name, defMapI M.! s) | (name, e) <- defs, s <- defSyms e ]
        defSyms e = S.toList (e `S.intersection` defNames)
        defMapI  = M.fromList (invert defMap)
        defMapF  = M.fromList defMap
        defMap   = zip [0..] (S.toList defNames)
        defNames = S.fromList (map fst defs)
        invert m = fmap (\(a,b) -> (b,a)) m

defOnly :: (Term -> a) -> DeclarationSyntax t -> Maybe (Name, a)
defOnly f (Definition name expr) = Just (name, f expr)
defOnly _ _                      = Nothing
