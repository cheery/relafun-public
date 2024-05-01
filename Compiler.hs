{-# LANGUAGE DataKinds, ImplicitParams, OverloadedStrings #-}
module Compiler where

import Lib.UnboundEff (Fresh', freshEff)
import Lib.Unify
import Unbound.Generics.LocallyNameless
import Data.Maybe (mapMaybe)
import Lib.ContEff
import Control.Monad (foldM)
import Data.Maybe (fromJust)
import Lib.Parser (quickParse)
import Syntax
import Lib.Graph (scc', preorder, buildG)
import Inference
import Implicits
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Backend as B
import qualified BackendWasm as BW
import qualified ToBackend as TB
import qualified Text.PrettyPrint as P
import System.Exit
import System.Environment
import Common

main = do
  args <- getArgs
  entry (args !! 0) (args !! 1)

entry inf outf = do
  text <- readFile inf
  case quickParse file text of
    Left err -> print err
    Right (name, decls) -> do
      let blocks = sccBlocks (mapMaybe (defOnly fv') decls)
      let ((tp,prog), err) = snd $ runEff'
                    $ runUnify initUnify
                    $ freshEff
                    $ writeToList @(Name Tm, InferenceError)
                    $ proceed blocks decls
      if length err /= 0
      then do print err
              exitWith (ExitFailure 0)
      else do let writer (x, y) = do
                    let x' = s2n (name2String x)
                    (y', bd) <- writeToList $ TB.toObj (M.empty) y
                    pure $ [(False, a, b) | (a,b) <- bd] <> [(True, x', Embed y')]
              let g = runEff' $ freshEff $ mapM writer prog
              mapM_ printTypeScheme (M.toList tp)
              mapM_ print prog
              mapM_ print g
              BW.compileFile outf (concat g)

printTypeScheme (name, Mono _) = print (P.text (show name) P.<+> ": mono")
printTypeScheme (name, Poly _ ty) = print (P.text (show name) P.<+> ":" P.<+> P.text (show ty))

proceed blocks decls = do
  foldM (declBlock decls) (M.empty, []) blocks

declBlock :: (Unify :< eff, Fresh' :< eff, Write (Name Tm, InferenceError) :< eff)
          => [DeclarationSyntax]
          -> (M.Map (Name Tm) Var, [(Name YTm, YTm)])
          -> [Name Tm]
          -> Eff eff (M.Map (Name Tm) Var, [(Name YTm, YTm)])
declBlock decls (types, prog) block = do
  let terms = filter (\(name,_) -> name `elem` block)
            $ mapMaybe (defOnly id) decls
  let perTerm (name, term)
        = do (Typing m ty ptm, errs) <- writeToList @InferenceError
                                      $ infer types term
             mapM (\err -> write (name, err)) errs
             Typing m' ty' ptm' <- generalize (Typing m ty ptm)
             ytm <- try $ implicits (ImEnv [] []) ptm'
             pure (name, s2n (name2String name), s2n (name2String name), ty', ynorm <$> ytm)
  schemes <- mapM perTerm terms
  pure (types <> M.fromList (map (\(x,z,_,y,_) -> (x,Poly z y)) schemes),
        prog <> mapMaybe (\(_,_,x,_,z) -> case z of Just z' -> Just (x,z')
                                                    Nothing -> Nothing) schemes)

sccBlocks :: [(Name t, S.Set (Name t))] -> [[Name t]]
sccBlocks defs = map (map (defMapF M.!) . preorder) (scc' graph)
  where graph     = buildG (0,maximum (map fst defMap)) edges
        edges     = [(defMapI M.! name, defMapI M.! s) | (name, e) <- defs, s <- defSyms e ]
        defSyms e = S.toList (e `S.intersection` defNames)
        defMapI  = M.fromList (invert defMap)
        defMapF  = M.fromList defMap
        defMap   = zip [0..] (S.toList defNames)
        defNames = S.fromList (map fst defs)
        invert m = fmap (\(a,b) -> (b,a)) m

defOnly :: (Tm -> a) -> DeclarationSyntax -> Maybe (Name Tm, a)
defOnly f (Definition name expr) = Just (name, f expr)
defOnly _ _                      = Nothing
