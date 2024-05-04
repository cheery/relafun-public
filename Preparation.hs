module Preparation (prepareModule) where

import Control.Lens
import Lib.ContEff
import Lib.UnboundEff (Fresh', freshEff)
import Common
import qualified Data.Set as S
import Unbound.Generics.LocallyNameless

prepareModule :: (Fresh' :< eff, Write Ident :< eff)
              => Module -> Eff eff Module
prepareModule mod = do (_, contents) <- unbind mod
                       (st, contents') <- state (S.empty :: S.Set Ident)
                                        $ go contents
                       pure $ bind (S.toList st) contents'
  where go contents = do
          mods <- mapM prepareSubModule (contents^.modules)
          mapM_ mem (contents^.values.to (map fst))
          spec <- prepareSpec (contents^.specification)
          pure (set modules mods
              . set specification spec
              $ contents)

prepareSpec spec = do
  ms <- mapM prepareSubModSig (spec^.moduleSigs)
  mapM_ memManifest (spec^.typeSigs.to (map (^._3)))
  mapM_ mem (spec^.typeSigs.to (map (^._1)))
  mapM_ mems (spec^.valueSigs.to (map (^._2)))
  pure (set moduleSigs ms
      $ spec)

memManifest (StructDecl bnd) = do
  (_, labels) <- unbind bnd
  mapM_ mem (labels^.to (map (^._1)))
memManifest _ = pure ()

prepareSubModSig (i, mt) = do
  mem i
  mt' <- prepareModType mt
  pure (i, mt')

prepareSubModule (i, term) = do
  mem i
  term' <- prepareModTerm term
  pure (i, term')

prepareModType :: (Write Ident :< eff, Fresh' :< eff) => ModType -> Eff eff ModType
prepareModType i@(MTIdent _) = pure i
prepareModType (Signature sig) = do
  (_, spec) <- unbind sig
  (st, spec') <- state (S.empty :: S.Set Ident) $ prepareSpec spec
  pure $ Signature (bind (S.toList st) spec')
prepareModType (ModFunctor bnd) = do
  ((name, Embed mt1), mt2) <- unbind bnd
  mt1' <- prepareModType mt1
  mt2' <- prepareModType mt2
  pure $ ModFunctor (bind (name, Embed mt1') mt2')

prepareModTerm i@(MIdent _) = pure i
prepareModTerm i@(MModule mod) = do
  mod' <- prepareModule mod
  pure (MModule mod')
prepareModTerm (MFunctor bnd) = do
  ((name, Embed mt), term) <- unbind bnd
  mt' <- prepareModType mt
  term' <- prepareModTerm term
  pure $ MFunctor (bind (name, Embed mt') term')
prepareModTerm (MApp f x) = MApp <$> prepareModTerm f <*> prepareModTerm x
prepareModTerm (MConstraint x mt)
  = MConstraint <$> prepareModTerm x <*> prepareModType mt

mem i = do seen <- get @(S.Set Ident)
           if S.member i seen
           then write i
           else put @(S.Set Ident) (S.insert i seen)

mems i = do seen <- get @(S.Set Ident)
            put @(S.Set Ident) (S.insert i seen)
