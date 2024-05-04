{-# LANGUAGE DataKinds, ImplicitParams, OverloadedStrings #-}
module Compiler where

import Control.Lens
import Lib.UnboundEff (Fresh', freshEff)
import Lib.Unify
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Data.Maybe (mapMaybe)
import Lib.ContEff
import Control.Monad (foldM)
import Data.Maybe (fromJust)
import Lib.Parser (quickParse)
import Syntax
import Lib.Graph (scc', preorder, buildG)
import Preparation
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
import Sub

main = do
  args <- getArgs
  entry (args !! 0) (args !! 1)

entry inf outf = do
  text <- readFile inf
  let result = runEff' $ catch $ freshEff $ do
       (name, mod) <- case quickParse file text of
                           Left err -> except (show err)
                           Right val -> pure val
       (mod', clashes) <- writeToList @Ident $ prepareModule mod
       case clashes of
         [] -> pure ()
         _  -> except ("name clashes: " <> show clashes)
       let (_, contents) = unsafeUnbind mod'
       let blocks = sccBlocks [(name, fv' tm) | (name, tm) <- contents^.values]
       -- TODO: proper preparation of the typing environment!
       let kinds = [(s2n "→", MKind (KType :->: (KType :->: KType)))]
       let aliasKinds (ident, kind, manifest) = (ident, MKind kind)
       let kinds' = kinds <> map aliasKinds (contents^.specification . typeSigs)
       let prepType (ins, name, ty) = do
            ty' <- tyMetaInst ty
            p <- try $ do k <- let ?kinds = kinds' in inferKind [] ty'
                          k =|= MKind KType
            case p of
              Nothing -> except @String "kind of error"
              Just _ -> do ty'' <- walk ty'
                           pure (ins, name, ty'')
       types <- fmap snd $ runUnify initUnify $ mapM prepType (contents^.specification . valueSigs)
       let typeMap = M.fromList [(name, Poly (s2n (name2String name)) ty)
                                | (ins, name, ty) <- types]
       let declBlock :: (Write (Ident, InferenceError) :< eff,
                         State (M.Map Ident Var, [(Name YTm, YTm)]) :< eff,
                         Fresh' :< eff)
                     => [Ident] -> Eff eff ()
           declBlock block = do
            (typeMap, progs) <- get @(M.Map Ident Var, [(Name YTm, YTm)])
            let terms = filter (\(name,_) -> elem name block) (contents^.values)
                perTerm (name'', term) = do
                  let name = s2n (name2String name'')
                  (Typing m ty ptm, errs) <- writeToList @InferenceError
                                           $ let ?typeMap = typeMap
                                             in infer M.empty term
                  mapM (\err -> write (name'', err)) errs
                  Typing m' ty' ptm' <- generalize (Typing m ty ptm)
                  case errs of
                    [] -> do let gamma = [(s2n (name2String name), s2n (name2String name))
                                         | name <- M.keys typeMap]
                             ytm <- try $ implicits (ImEnv [] gamma) ptm'
                             pure (s2n (name2String name), s2n (name2String name), s2n (name2String name), ty', ynorm . yerase <$> ytm)
                    _ -> pure (s2n (name2String name), s2n (name2String name), s2n (name2String name), ty', Nothing)
            let valuesOnly (name, Value v) = Just (name, v)
                valuesOnly _ = Nothing
            schemes <- fmap snd $ runUnify initUnify $ mapM perTerm $ mapMaybe valuesOnly terms
            let types' = M.fromList (map (\(x,z,_,y,_) -> (x,Poly z y)) schemes)
            let progs' = mapMaybe (\(_,_,x,_,z) -> case z of Just z' -> Just (x,z')
                                                             Nothing -> Nothing) schemes
            put @(M.Map Ident Var, [(Name YTm, YTm)])
              $ (types' <> typeMap, progs <> progs')
       ((tp,prog), ((), err)) <- state (typeMap, [] :: [(Name YTm, YTm)])
                               $ writeToList @(Ident, InferenceError)
                               $ mapM_ declBlock blocks
       if length err /= 0 then except (show err) else pure()
       let writer (x, y) = do
             let x' = s2n (name2String x)
             (y', bd) <- writeToList @(Name B.Atom, Embed B.Obj) $ TB.toObj (M.empty) y
             pure $ [(False, a, b) | (a,b) <- bd] <> [(True, x', Embed y')]
       g <- mapM writer prog
       let subType (name, st) = (name, unignore st)
           subtypes = contents^.specification . subTypeSigs . to (map subType)
           subFunc (name, ValueSubFunction sf) = Just (name, unignore sf)
           subFunc _ = Nothing
           subfunctions = contents^.values.to (mapMaybe subFunc)
       pure (BW.compileFile outf
                            subtypes
                            (concat g)
                            [(s2n (name2String n), f) | (n,f) <- subfunctions])
  case result of
    Left msg -> do putStrLn msg
                   exitWith (ExitFailure (-1))
    Right output -> output

{--
      let types = decls^.typeDecls
      let aliases = decls^.typeAliases
      let subtypes = decls^.subTypes
      let subfunctions = decls^.subFunctions

printTypeScheme (name, Mono _) = print (P.text (show name) P.<+> ": mono")
printTypeScheme (name, Poly _ ty) = print (P.text (show name) P.<+> ":" P.<+> P.text (show ty))

--}

sccBlocks :: [(Name t, S.Set (Name t))] -> [[Name t]]
sccBlocks [] = []
sccBlocks defs = map (map (defMapF M.!) . preorder) (scc' graph)
  where graph     = buildG (0,maximum (map fst defMap)) edges
        edges     = [(defMapI M.! name, defMapI M.! s) | (name, e) <- defs, s <- defSyms e ]
        defSyms e = S.toList (e `S.intersection` defNames)
        defMapI  = M.fromList (invert defMap)
        defMapF  = M.fromList defMap
        defMap   = zip [0..] (S.toList defNames)
        defNames = S.fromList (map fst defs)
        invert m = fmap (\(a,b) -> (b,a)) m
