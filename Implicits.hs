module Implicits where

import Lib.ContEff
import Lib.Unify
import Lib.UnboundEff (Fresh', freshEff)
import Unbound.Generics.LocallyNameless
import Common
import qualified Data.Set as S

rename name = fresh (s2n (name2String name))

translate :: PTm -> Maybe YTm
translate p = runEff' (try (freshEff (implicits (ImEnv [] []) p)))

data ImEnv = ImEnv {
               getPEta :: [(Ty, Name YTm)],
               getPGamma :: [(Name PTm, Name YTm)] }
             deriving (Show)

implicits :: (Fresh' :< eff, Abort :< eff)
          => ImEnv -> PTm -> Eff eff YTm
implicits env (PVar x) | Just y <- lookup x (getPGamma env) = pure (YVar y)
                       | otherwise = error ("lookup failed: " <> show x <> " env: " <> show env)
implicits env (PLit i) = pure (YLit i)
implicits env (PLam bnd) = do
  ((name,Embed c), body) <- unbind bnd
  name' <- rename name
  let env' = env { getPGamma = (name,name') : getPGamma env }
  body' <- implicits env' body
  pure $ YLams (bind ([], [(name', Embed c)]) body')
implicits env (PApp f x) = do
  (\f x -> YApps f [] [x]) <$> implicits env f <*> implicits env x
implicits env (PTLam bnd) = do
  (n, body) <- unbind bnd
  YLams . bind ([n], []) <$> implicits env body
implicits env (PTApp f t) = do
  (\f x -> YApps f [x] []) <$> implicits env f <*> pure t
implicits env (PILam bnd) = do
  ((name, Embed p), e) <- unbind bnd
  name' <- rename name
  let env' = env { getPEta = (p,name') : getPEta env }
  e' <- implicits env' e
  pure $ YLams (bind ([], [(name', Embed p)]) e')
implicits env (PIApp f x) = do
  (\f x -> YApps f [] [x]) <$> implicits env f <*> implicits env x
implicits env (PQuery p) = query env p

query :: (Fresh' :< eff, Abort :< eff)
      => ImEnv -> Ty -> Eff eff YTm
query env (TAll bnd) = do
  ((name, mkind), p) <- unbind bnd
  YLams . bind ([(name, mkind)], []) <$> query env p
query env (TRule p1 p2) = do
  name' <- fresh (s2n "r")
  let env' = env { getPEta = (p1,name') : getPEta env }
  YLams . bind ([], [(name', Embed p1)]) <$> query env' p2
query env t = do
  (rs, ws, e) <- matchesFirst env t
  rs' <- mapM (query env) rs
  pure $ foldr (\(w,r) e -> subst w r e) e (zip ws rs')

matchesFirst :: (Fresh' :< eff, Abort :< eff)
             => ImEnv -> Ty -> Eff eff ([Ty], [Name YTm], YTm)
matchesFirst env t = mysum [matches r t x | (r, x) <- getPEta env]

mysum [] = abort
mysum (x:xs) = do c <- try x
                  case c of
                    Just x -> pure x
                    Nothing -> mysum xs

matches :: (Fresh' :< eff, Abort :< eff)
        => Ty -> Ty -> Name YTm -> Eff eff ([Ty], [Name YTm], YTm)
matches r t x = fmap snd $ runUnify initUnify $ go r [] [] [] [] (YVar x)
  where go (TAll bnd) recs vars evs ns term = do
          ((name, Embed mkind), c1) <- unbind bnd
          pt <- TMeta <$> freshMeta mkind
          let c1' = subst name pt c1
          go c1' recs (pt : vars) evs (name:ns) (YApps term [TVar name] [])
        go (TRule cx r) recs vars evs ns term = do
          name <- fresh (s2n "r")
          go r (cx : recs) vars (name : evs) ns (YApps term [] [YVar name])
        go t' recs vars evs ns term = do
          t === t'
          recs' <- mapM walk recs
          vars' <- mapM walk vars
          let term' = foldr (\(w,r) e -> subst w r e) term (zip ns vars')
          pure (recs, evs, term')
