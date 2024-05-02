module ToBackend where

import Unbound.Generics.LocallyNameless
import Lib.ContEff
import Lib.UnboundEff (Fresh', freshEff)
import qualified Backend as B
import Common
import qualified Data.Set as S
import qualified Data.Map as M
import Lib.Unify (fv')

-- We go gradually from proto objects to backend objects.
data ProtoObj = PFun (S.Set (Name B.Atom)) (Bind [Name B.Atom] B.Expr)
              | PPap B.Atom [B.Atom]
              | PExpr (S.Set (Name B.Atom)) B.Expr
              | PAtom (S.Set (Name B.Atom)) EnvAtom

-- Environment atoms have arity marked to them when it's known.
data EnvAtom = EAtom B.Atom
             | EFunc Arity B.Atom
type Arity = Int

arity :: EnvAtom -> Maybe Arity
arity (EAtom _) = Nothing
arity (EFunc c _) = Just c

setify :: M.Map k EnvAtom -> S.Set (Name B.Atom)
setify = S.unions . fmap (fv' . unbox)

isAtom :: YTm -> Bool
isAtom (YVar _) = True
isAtom (YLit _) = True
isAtom _        = False
 
isPap (Just a) b = b < a
isPap _        _ = False

-- The next step is to generate proto objects.
pobj :: (Write (Name B.Atom, Embed B.Obj) :< eff,
         Fresh' :< eff)
     => M.Map (Name YTm) EnvAtom -> YTm -> Eff eff ProtoObj
pobj env (YLams bnd) = do
  ((_, ys), body) <- unbind bnd
  let names = map fst ys
  anames <- mapM (\_ -> fresh (s2n "p")) names
  let env' = env <> M.fromList (zip names (map (EAtom . B.Var) anames))
  body' <- toExpr env' body
  pure (PFun (setify env) (bind anames body'))
pobj env (YApps f _ xs) = do
  ((callee, args), bd) <- writeToList @(Name B.Atom, Embed B.Obj)
     $ do callee <- atomize env f
          args <- mapM (atomize env) xs
          pure (callee, map unbox args)
  if isPap (arity callee) (length args)
  then do mapM_ write bd
          pure (PPap (unbox callee) args)
  else pure $ PExpr (setify env) $ blet bd $ B.Apply (unbox callee) args
pobj env (YLet bnd) = do
  ((name, _, Embed tm1), tm2) <- unbind bnd
  a <- if isAtom tm1
       then do a' <- pobj env tm1
               case a' of
                 PAtom _ a -> pure a
       else do n <- fresh (s2n (name2String name))
               hoist env n tm1
  pobj (M.insert name a env) tm2
pobj env (YVar n) | Just m <- M.lookup n env = pure $ PAtom (setify env) m
                  | otherwise = pure $ PAtom (setify env) (EAtom $ B.Var $ s2n (name2String n))
pobj env (YLit i) = pure $ PAtom (setify env) (EAtom $ B.Lit31i i)
                               
hoist :: (Write (Name B.Atom, Embed B.Obj) :< eff, Fresh' :< eff)
      => M.Map (Name YTm) EnvAtom -> Name B.Atom -> YTm -> Eff eff EnvAtom
hoist env name t
  = do o <- pobj env t
       write (name, Embed (mk o))
       case o of
         PFun _ bnd -> do (c, _) <- unbind bnd
                          pure $ EFunc (length c) (B.Var name)
         _        -> pure $ EAtom (B.Var name)

atomize :: (Write (Name B.Atom, Embed B.Obj) :< eff, Fresh' :< eff)
        => M.Map (Name YTm) EnvAtom -> YTm -> Eff eff EnvAtom
atomize env term = if isAtom term
                   then do o <- pobj env term
                           case o of
                                PAtom _ a -> pure a
                   else do name <- fresh (s2n "a")
                           hoist env name term
                           

toObj env term = (mk <$> pobj env term)

toExpr env term = do
  (p, bd) <- writeToList @(Name B.Atom, Embed B.Obj)
           $ pobj env term
  case p of
      PExpr _ e -> pure (blet bd e)
      PAtom _ a -> pure (blet bd (B.Atom$unbox a))
      o         -> do name <- fresh (s2n "o")
                      pure (blet (bd<>[(name,Embed (mk o))])
                                 (B.Atom (B.Var name)))

-- Turns the proto obj to real obj
mk (PFun s bnd) = B.fun s bnd
mk (PPap f xs) = B.Pap f xs
mk (PExpr s e) = B.thunk s e
mk (PAtom s a) = B.thunk s (B.Atom (unbox a))

blet [] e = e
blet (b:bd) e = B.Let (bind b (blet bd e))

-- Operations on environment atoms.
unbox :: EnvAtom -> B.Atom
unbox (EAtom a) = a
unbox (EFunc _ a) = a
