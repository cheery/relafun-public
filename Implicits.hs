module ToF where

import Lib.ContEff
import Lib.Unify
import Lib.UnboundEff (Fresh', freshEff)
import Unbound.Generics.LocallyNameless
import Common
import qualified Data.Set as S

rename name = fresh (s2n (name2String name))

translatePContext :: (Fresh' :< eff, Abort :< eff) => [(PCtxN, FTyN)] -> PCtx -> Eff eff FTy
translatePContext cx (PCType t) = translatePType cx t
translatePContext cx (PCAll bnd)
  = do (name, f) <- unbind bnd
       name' <- rename name
       FTAll . bind name' <$> translatePContext ((name,name'):cx) f
translatePContext cx (PCRule c1 c2)
  = FTFun <$> translatePContext cx c1 <*> translatePContext cx c2

translatePType :: (Fresh' :< eff, Abort :< eff) => [(PCtxN, FTyN)] -> PTy -> Eff eff FTy
translatePType cx (PTVar a) | Just b <- lookup a cx = pure $ FTVar b
translatePType cx (PTMVar _) = abort
translatePType cx (PTSym s) = pure $ FTSym s
translatePType cx (PTFun c1 c2) = 
  FTFun <$> translatePContext cx c1 <*> translatePContext cx c2

translate :: PTm -> Maybe FTm
translate p = runEff' (try (freshEff (translatePTm (TransEnv [] [] []) p)))

data TransEnv = TransEnv {
                  getPEta :: [(PCtx, FTmN)],
                  getPDelta :: [(PCtxN, FTyN)],
                  getPGamma :: [(PTmN, FTmN)] }

translatePTm :: (Fresh' :< eff, Abort :< eff)
             => TransEnv -> PTm -> Eff eff FTm
translatePTm env (PVar x) | Just y <- lookup x (getPGamma env) = pure (FVar y)
translatePTm env (PLit i) = pure (FLit i)
translatePTm env (PLam bnd) = do
  ((name,Embed c), body) <- unbind bnd
  name' <- rename name
  let env' = env { getPGamma = (name,name') : getPGamma env }
  body' <- translatePTm env body
  ty <- translatePContext (getPDelta env) c
  pure $ FLam (bind (name', Embed ty) body')
translatePTm env (PApp f x) = do
  FApp <$> translatePTm env f <*> translatePTm env x
translatePTm env (PTLam bnd) = do
  (name, body) <- unbind bnd
  name' <- rename name
  let env' = env { getPDelta = (name,name') : getPDelta env }
  FTLam . bind name' <$> translatePTm env' body
translatePTm env (PTApp f t) = do
  FTApp <$> translatePTm env f <*> translatePContext (getPDelta env) t
translatePTm env (PILam bnd) = do
  ((name, Embed p), e) <- unbind bnd
  name' <- rename name
  t <- translatePContext (getPDelta env) p
  let env' = env { getPEta = (p,name') : getPEta env }
  e' <- translatePTm env' e
  pure $ FLam (bind (name', Embed t) e')
translatePTm env (PIApp f x) = do
  FApp <$> translatePTm env f <*> translatePTm env x
translatePTm env (PQuery p) = translateQuery env p

translateQuery :: (Fresh' :< eff, Abort :< eff)
               => TransEnv -> PCtx -> Eff eff FTm
translateQuery env (PCAll bnd) = do
  (name, p) <- unbind bnd
  name' <- rename name
  let env' = env { getPDelta = (name,name') : getPDelta env }
  FTLam . bind name' <$> translateQuery env' p
translateQuery env (PCRule p1 p2) = do
  name' <- fresh (s2n "r")
  let env' = env { getPEta = (p1,name') : getPEta env }
  ty <- translatePContext (getPDelta env) p1
  FLam . bind (name', Embed ty) <$> translateQuery env' p2
translateQuery env (PCType t) = do
  (rs, ws, e) <- matchesFirst env t
  rs' <- mapM (translateQuery env) rs
  pure $ foldr (\(w,r) e -> subst w r e) e (zip ws rs')

matchesFirst :: (Fresh' :< eff, Abort :< eff)
             => TransEnv -> PTy -> Eff eff ([PCtx], [FTmN], FTm)
matchesFirst env t = mysum [matches (getPDelta env) r t x | (r, x) <- getPEta env]

mysum [] = abort
mysum (x:xs) = do c <- try x
                  case c of
                    Just x -> pure x
                    Nothing -> mysum xs

matches :: (Fresh' :< eff, Abort :< eff)
        => [(PCtxN, FTyN)] -> PCtx -> PTy -> FTmN -> Eff eff ([PCtx], [FTmN], FTm)
matches env r t x = fmap snd $ runUnify @PCtx initUnify $ go r [] [] [] [] (FVar x)
  where go (PCType t') recs vars evs ns term = do
          (PCType t) === (PCType t')
          recs' <- mapM walk recs
          vars' <- mapM walk vars
          vars'' <- mapM (translatePContext env) vars'
          let term' = foldr (\(w,r) e -> subst w r e) term (zip ns vars'')
          pure (recs, evs, term')
        go (PCAll bnd) recs vars evs ns term = do
          (name, c1) <- unbind bnd
          name' <- rename name
          pt <- PCType . PTMVar <$> freshMeta
          let c1' = subst name pt c1
          go c1' recs (pt : vars) evs (name':ns) (FTApp term (FTVar name'))
        go (PCRule cx r) recs vars evs ns term = do
          name <- fresh (s2n "r")
          go r (cx : recs) vars (name : evs) ns (FApp term (FVar name))
