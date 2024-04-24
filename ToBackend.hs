module ToBackend where

import Lib.ContEff
import Syntax
import qualified Backend as B

-- We go gradually from proto objects to backend objects.
data ProtoObj = PFun [B.Id] B.Expr
              | PPap B.Atom [B.Atom]
              | PExpr B.Expr
              | PAtom EnvAtom

-- Environment atoms have arity marked to them when it's known.
data EnvAtom = EAtom B.Atom
             | EFunc Arity B.Atom
type Arity = Int

arity :: EnvAtom -> Maybe Arity
arity (EAtom _) = Nothing
arity (EFunc c _) = Just c

-- First of all, we determine how many objects are being hoisted in expression.
hoistc :: Int -> [Maybe Arity] -> Term -> Int
hoistc k env (Lam name body) = 0
hoistc k env (App f x) = let args = unwind f [x]
                             tip  = applyTip f
                         in if isPap (arityOf env tip) (length args)
                            then sum (map (hoistc 0 env) (tip:args))
                            else k
hoistc k env (Let n t b) = (if isAtom b then 1 else 0)
                         + hoistc k (arityOf env t:env) b
hoistc k env (Sym n) = 0
hoistc k env (Var i) = 0
hoistc k env (Lit n) = 0

arityOf env (Lam name body) = Just (length (unroll body) + 1)
arityOf env (Let n t b)     = arityOf (arityOf env t:env) b
arityOf env (Var i)         = env !! i
arityOf env _               = Nothing

isExpr :: [Maybe Arity] -> Term -> Bool
isExpr env (Let n t b)      = isExpr (arityOf env t:env) b
isExpr env (App f x) = let args = unwind f [x]
                           tip = applyTip f
                       in not (isPap (arityOf env tip) (length args))
isExpr env (Sym _) = True
isExpr env (Var _) = True
isExpr env (Lit _) = True

isAtom :: Term -> Bool
isAtom (Sym _) = True
isAtom (Var _) = True
isAtom (Lit _) = True
isAtom _       = False

-- Utility functions
unwind (App f x) xs = unwind f (x:xs)
unwind other     xs = xs

applyTip (App f _) = applyTip f
applyTip o         = o

unroll (Lam name body) = name:unroll body
unroll other           = []

lamTip (Lam name body)    = lamTip body
lamTip other              = other

isPap (Just a) b = b < a
isPap _        _ = False

-- The next step is to generate proto objects.
pobj :: (Write B.Bind :< eff,
         State B.DebruijnIndex :< eff)
     => [EnvAtom] -> Term -> Eff eff ProtoObj
pobj env (Lam name body) = do
  let names = name:unroll body
      env' = map (\i -> EAtom (B.Var i)) [0..length names - 1]
          <> map (shift (length names)) env
  pure (PFun names (toExpr env' (lamTip body)))
pobj env (App f x) = do
  let args = unwind f [x]
      f'   = applyTip f
      aenv = map arity env
  if isPap (arityOf aenv f') (length args)
  then do
    callee <- atomize env f'
    arglist <- mapM (atomize env) args
    pure (PPap callee arglist)
  else do
    let hc = hoistc 1 aenv f' + sum (map (hoistc 1 aenv) args)
        blet ((0, p),[]) = PExpr p
        blet ((0, p),bd) = PExpr (B.Let bd p)
        blet ((n, p),bd) = error$"blet " <> show n <> " at " <> show (f', args) <> "hc=" <> show hc
        env' = map (shift hc) env
    pure $ blet $ runEff'
         $ writeToList @B.Bind
         $ state @B.DebruijnIndex hc
         $ do callee <- atomize env' f'
              arglist <- mapM (atomize env') args
              pure (B.Apply callee arglist)
pobj env (Let n t b) = if isAtom t
                       then do a' <- pobj env t
                               case a' of
                                 PAtom a -> pobj (a:env) b
                       else do a <- hoist env n t
                               pobj (a:env) b
pobj env (Sym n) = pure$PAtom (EAtom $ B.Sym n)
pobj env (Var i) = pure$PAtom (env !! i)
pobj env (Lit i) = pure$PAtom (EAtom $ B.Lit31i i)
                               
hoist :: (Write B.Bind :< eff,
          State B.DebruijnIndex :< eff)
      => [EnvAtom] -> B.Id -> Term -> Eff eff EnvAtom
hoist env name t
  = do n <- get
       let m = n - 1
       put m
       o <- pobj (map (shift (-n)) env) t
       write @B.Bind (name, mk o)
       case o of
         PFun c _ -> pure$EFunc (length c) (B.Var m) 
         _        -> pure$EAtom (B.Var m)

atomize :: (Write B.Bind :< eff,
            State B.DebruijnIndex :< eff)
        => [EnvAtom] -> Term -> Eff eff B.Atom
atomize env term = if isAtom term
                   then do o <- pobj env term
                           case o of
                                PAtom a -> pure (unbox a)
                   else do a <- hoist env "" term
                           pure (unbox a)

toObj env term = let hc = hoistc 0 (map arity env) term
                 in if hc == 0
                    then let ((0, p),[]) = runEff'                 
                                         $ writeToList @B.Bind
                                         $ state @B.DebruijnIndex hc
                                         $ pobj env term
                         in case p of
                            PFun c e -> B.fun c e
                            PPap f x -> B.Pap f x
                            PExpr e  -> B.thunk e
                            PAtom a  -> B.thunk (B.Atom$unbox a)
                    else B.thunk (toExpr env term)
                    
toExpr env term = let hd = hoistc 0 (map arity env) term
                      hc = hd
                         + (if isExpr (map arity env) term then 0 else 1)
                      ((k, p),bd) = runEff'
                             $ writeToList @B.Bind
                             $ state @B.DebruijnIndex hc
                             $ pobj (map (shift hd) env) term
                      blet 0 [] e = e
                      blet 0 bd e = B.Let bd e
                      blet n bd p = error$"blet " <> show n <> " at " <> show term <> "hc=" <> show hc
                  in case p of
                       PExpr e -> blet k bd e
                       PAtom a -> blet k bd (B.Atom$unbox a)
                       o       -> blet (k-1) (bd<>[("",mk o)]) (B.Atom (B.Var 0))

mk (PFun n e) = B.fun n e
mk (PPap f xs) = B.Pap f xs
mk (PExpr e) = B.thunk e
mk (PAtom a) = B.thunk (B.Atom (unbox a))

-- Operations on environment atoms.
unbox :: EnvAtom -> B.Atom
unbox (EAtom a) = a
unbox (EFunc _ a) = a

shift :: B.DebruijnIndex -> EnvAtom -> EnvAtom
shift i (EAtom a) = EAtom (shiftAtom i a)
shift i (EFunc c a) = EFunc c (shiftAtom i a)

shiftAtom :: B.DebruijnIndex -> B.Atom -> B.Atom
shiftAtom i (B.Var j) = B.Var (i+j)
shiftAtom i other     = other

demo1 :: [(Name, Term)]
demo1 = [
  ("I", Lam "x" (Var 0)),
  ("K", Lam "x" (Lam "y" (Var 1))),
  ("S", Lam "x" (Lam "y" (Lam "z"
        (App (App (Var 2) (Var 0))
             (App (Var 1) (Var 0)))))) ]
