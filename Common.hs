module Common where

import Data.Maybe (mapMaybe)
import Lib.ContEff
import Lib.UnboundEff (Fresh', freshEff)
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import GHC.Generics
import Data.Typeable (Typeable)
import Lib.Unify
import qualified Data.Set as S
import qualified Data.Map as M
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)
import Data.Dynamic

-- Ideas from: https://github.com/magnatelee/implicitcalculus/

data Ty
  = TVar (Name Ty)
  | TMeta (MVar MKind Ty)
  | TRField String Ty Ty
  | TREnd
  | TFAbsent
  | TFPresent [Ty]
  | (:$:) Ty Ty
  | TAll (Bind (Name Ty, Embed MKind) Ty)
  | TRule Ty Ty
  deriving (Show, Generic, Typeable)

instance Alpha Ty
instance Alpha MKind
instance Alpha Kind

instance Subst Ty Kind
instance Subst Ty MKind
instance Subst Ty Ty where
  isvar (TVar n) = Just (SubstName n)
  isvar _ = Nothing

instance Unifiable (Bind (Name Ty, Embed MKind) Ty) where
  walk bnd = do ((name, Embed kind), ty) <- unbind bnd
                kind' <- walk kind
                ty' <- walk ty
                pure (bind (name, Embed kind') ty')
  autounify x y = do
    ((n1, Embed k1), t1) <- unbind x
    ((n2, Embed k2), t2) <- unbind y
    n3 <- fresh (s2n "tmp")
    let t1' = subst n1 (TVar n3) t1
        t2' = subst n1 (TVar n3) t2
    a <- autounify k1 k2
    b <- autounify t1' t2'
    let c :: [MVar MKind Ty] = mapMaybe fromDynamic b
    values <- mapMaybe id <$> mapM getValue c
    if n3 `S.member` S.unions (map fv' values)
    then abort
    else pure (a <> b)
  metafold f x bnd = let ((name, Embed kind), ty) = unsafeUnbind bnd
                     in metafold f (metafold f x ty) kind

-- We only need to act if we're dealing with row fields.
isRowMeta :: Ty -> Bool
isRowMeta (TRField _ _ _) = True
isRowMeta _ = False

rmeta :: (Unify :< eff) => Ty -> Eff eff (Maybe (MVar MKind Ty), M.Map String Ty)
rmeta TREnd = pure (Nothing, M.empty)
rmeta (TMeta i) = do mrow <- getMRow <$> getMeta i
                     case mrow of
                       Left _ -> pure (Nothing, M.empty)
                       Right a -> pure (Just i, M.fromList (map (,TFAbsent) (S.toList a)))
rmeta (TRField n a b) = do (i, m) <- rmeta b
                           pure (i, M.insert n a m)
rmeta _ = pure (Nothing, M.empty)

instance Unifiable Ty where
  unify (TMeta i) (TMeta j) | (i /= j) = Just $ do
    k1 <- getMRow <$> getMeta i
    k2 <- getMRow <$> getMeta j
    let k3 = (<>) <$> k1 <*> k2
    val <- TMeta <$> freshMeta (putMRow k3)
    ext i val
    ext j val
    pure [toDyn i, toDyn j]
  unify a b | isRowMeta a || isRowMeta b = Just $ do
    (mi, aa) <- rmeta a
    (mj, bb) <- rmeta b
    mapM_ id (M.intersectionWith autounify aa bb)
    top <- isClosed mi mj (S.fromList (M.keys (aa <> bb)))
    xs <- brush mi (M.toList (M.difference bb aa)) top
    ys <- brush mj (M.toList (M.difference aa bb)) top
    pure (xs <> ys)
    where brush Nothing [] top = pure []
          brush (Just i) vec top = ext i (expand vec top) >> pure [toDyn i]
          brush _ _ _ = abort
          expand [] top = top
          expand ((_, TFAbsent):vs) top = expand vs top
          expand ((n, other):vs) top = TRField n other (expand vs top)
          isClosed Nothing _       _ = pure TREnd
          isClosed _       Nothing _ = pure TREnd
          isClosed _       _       common = TMeta <$> freshMeta (putMRow (Right common))
  unify (TMeta i) t = Just $ do ext i t
                                pure [toDyn i]
  unify t (TMeta i) = Just $ do ext i t
                                pure [toDyn i]
  unify _ _ = Nothing
  walklocal m@(TMeta i) = Just $ (maybe m id <$> getValue i)
  walklocal _ = Nothing

data MKind
  = MKind Kind
  | MRow [String]
  deriving (Show, Eq, Generic, Typeable)

instance Unifiable a => Unifiable (Ignore a)
instance Unifiable (S.Set String) where
  walk u = pure u
  autounify a b = if a == b then pure []
                            else abort
  metafold _ x _ = x
instance Unifiable MKind

data Kind
  = (:->:) Kind Kind
  | KMeta (MVar () Kind)
  | KRow
  | KField
  | KType
  deriving (Show, Eq, Generic, Typeable)

-- Why the unsymmetry?
-- The logic behind this is that KRow is reserved for closed rows.
-- Thought there can be inferred or blank metavariables
-- that are MKind KRow.
getMRow :: MKind -> Either Kind (S.Set String)
getMRow (MKind KRow) = Right S.empty
getMRow (MKind t)    = Left t
getMRow (MRow a)     = Right (S.fromList a)

putMRow (Left t) = MKind t
putMRow (Right a) = MRow (S.toAscList a)

instance Unifiable Kind where
  unify (KMeta i) t = Just $ do ext i t
                                pure [toDyn i]
  unify t (KMeta i) = Just $ do ext i t
                                pure [toDyn i]
  unify _ _ = Nothing
  walklocal m@(KMeta i) = Just $ (maybe m id <$> getValue i)
  walklocal _ = Nothing

-- Source language level terms.
data Tm
  = Var (Name Tm)
  | Lam (Bind (Name Tm) Tm)
  | Let (Bind (Name Tm, Embed Tm) Tm)
  | App Tm Tm
  | Lit Integer
  deriving (Show, Generic, Typeable)

instance Alpha Tm

data PTm
  = PVar (Name PTm)
  | PLam (Bind (Name PTm, Embed Ty) PTm)
  | PLet (Bind (Name PTm, Embed Ty, Embed PTm) PTm)
  | PApp PTm PTm
  | PTLam (Bind (Name Ty, Embed MKind) PTm)
  | PTApp PTm Ty
  | PQuery Ty
  | PILam (Bind (Name PTm, Embed Ty) PTm)
  | PIApp PTm PTm
  | PLit Integer
  deriving (Show, Generic, Typeable)

instance Unifiable (Embed Ty)
instance Unifiable (Embed PTm)
instance Unifiable (Embed MKind)
instance Unifiable (Name PTm, Embed Ty, Embed PTm)
instance Unifiable (Bind (Name PTm, Embed Ty, Embed PTm) PTm)
instance Unifiable (Name PTm, Embed Ty)
instance Unifiable (Bind (Name PTm, Embed Ty) PTm)
instance Unifiable (Name Ty, Embed MKind)
instance Unifiable (Bind (Name Ty, Embed MKind) PTm)
instance Unifiable PTm
instance Alpha PTm

-- Nearly the last stage before we reach the backend.
data YTm
  = YVar (Name YTm)
  | YLit Integer
  | YLet (Bind (Name YTm, Embed Ty, Embed YTm) YTm)
  | YLams (Bind ([(Name Ty, Embed MKind)], [(Name YTm, Embed Ty)]) YTm)
  | YApps YTm [Ty] [YTm]
  deriving (Show, Generic, Typeable)

instance Alpha YTm
instance Subst YTm Ty
instance Subst YTm Kind
instance Subst YTm MKind
instance Subst YTm YTm where
  isvar (YVar n) = Just (SubstName n)
  isvar _ = Nothing
instance Subst Ty YTm

ynorm :: YTm -> YTm
ynorm (YVar name) = YVar name
ynorm (YLit i) = YLit i
ynorm (YLet bnd) = YLet (bind (name, ty, Embed (ynorm tm1)) (ynorm tm2))
  where ((name, ty, Embed tm1), tm2) = unsafeUnbind bnd
ynorm (YLams bnd) = case extractLam body of
                         Just ((xs', ys'), body) -> ynorm (YLams (bind (xs <> xs', ys <> ys') body))
                         Nothing -> YLams (bind (xs, ys) (ynorm body))
  where ((xs, ys), body) = unsafeUnbind bnd
        extractLam (YLams bnd) = Just (head, body)
           where (head, body) = unsafeUnbind bnd
        extractLam (YLet bnd) | (block, body) <- unsafeUnbind bnd
                              , Just (head, body) <- extractLam body = Just (head, YLet (bind block body))
        extractLam _ = Nothing
ynorm (YApps f xs ys) = case extractApp f id of
                             Just (f, xs', ys', wrap) -> ynorm (wrap (YApps f (xs' <> xs) (ys' <> ys)))
                             Nothing -> YApps (ynorm f) xs (map ynorm ys)
  where extractApp (YApps f xs ys) wrap = Just (f, xs, ys, wrap)
        extractApp (YLet bnd) wrap | (block, body) <- unsafeUnbind bnd
                                   , Just (f, xs, ys, wrap) <- extractApp body wrap = Just (f, xs, ys, YLet . bind block . wrap)
        extractApp _ _ = Nothing
        

-- TODO: Implement termination checking for rules
-- TODO: Reimplement Compiler.hs

{--
-- System F, soon to be demantled


instance Subst FTm FTy
instance Subst FTy FTm
instance Subst FTm FTm where
instance Subst FTy FTy where
  isvar (FTVar n) = Just (SubstName n)
  isvar _ = Nothing

-- Type checking for system F
type Delta = [ FTyN ]
type Gamma = [ (FTmN, FTy) ]

checkTyVar :: (Write String :< eff,
               Abort :< eff)
           => Delta -> FTyN -> Eff eff ()
checkTyVar delta v
  = if elem v delta
    then pure ()
    else (write $ "NotFound: " <> show v) >> abort

lookupTmVar :: (Write String :< eff,
                Abort :< eff)
            => Gamma -> FTmN -> Eff eff FTy
lookupTmVar gamma v
  = case lookup v gamma of
      Just s -> pure s
      Nothing -> (write $ "NotFound: " <> show v) >> abort

tcty :: (Write String :< eff,
         Abort :< eff,
         Fresh' :< eff)
     => Delta -> Gamma -> FTy -> Eff eff ()
tcty d g (FTVar alpha) = checkTyVar d alpha
tcty d g (FTSym name) = pure ()
tcty d g (FTFun a b) = tcty d g a
                    >> tcty d g b
tcty d g (FTAll bnder) = do
  (alpha, ty') <- unbind bnder
  tcty (alpha:d) g ty'

ti :: (Write String :< eff,
       Abort :< eff,
       Fresh' :< eff)
   => Delta -> Gamma -> FTm -> Eff eff FTy
ti d g (FVar v) = lookupTmVar g v
ti d g (FSym s) = undefined
ti d g (FLit i) = undefined
ti d g (FLet t b) = undefined
ti d g (FLam bnd) = do
  ((alpha, Embed ty), t) <- unbind bnd
  tcty d g ty
  ty' <- ti d ((alpha,ty):g) t
  pure (FTFun ty ty')
ti d g (FApp f x) = do
  ty1 <- ti d g f
  ty2 <- ti d g x
  case ty1 of
    FTFun a b | aeq a ty2 -> pure b
    _ -> write "type error (App)" >> abort
ti d g (FTLam bnd) = do
  (v, t) <- unbind bnd
  ty <- ti (v:d) g t
  pure (FTAll (bind v ty))
ti d g (FTApp f ty) = do
  tyf <- ti d g f
  case tyf of
    (FTAll bnder) -> do
      tcty d g ty
      pure (substBind bnder ty)
    _ -> write "type error (Forall)" >> abort

-- Intermediate language
type PCtxN = Name PCtx
type PTmN = Name PTm

data PTy
  = PTVar PCtxN
  | PTMVar (MVar () PCtx)
  | PTSym String
  | PTFun PCtx PCtx
  deriving (Show, Generic, Typeable)

data PCtx
  = PCType PTy
  | PCAll (Bind PCtxN PCtx)
  | PCRule PCtx PCtx
  deriving (Show, Generic, Typeable)

{--
instance Unifiable PCtx (Bind PCtxN PCtx) where
  unify x y = do
    s <- fresh (s2n "skolem")
    let x' = substBind x (PCType (PTVar s))
        y' = substBind y (PCType (PTVar s))
    r :: Maybe (UnifySubst PCtx) <- unify' x' y'
    case r of
      Nothing -> pure Nothing
      Just m -> if S.member s (foldr (\x y -> (S.fromList . toListOf fv) x <> y) S.empty m)
                then pure (Just m)
                else pure Nothing

instance Unifiable PCtx PTy
instance Unifiable PCtx PCtx where
  walkvar (PCType (PTMVar m)) = Just (m, id)
  unify (PCType (PTMVar m)) other = pure (ext m other M.empty)
  unify other (PCType (PTMVar m)) = pure (ext m other M.empty)
  unify _ _                       = pure Nothing

instance Subst PCtx PTy
instance Subst PCtx PCtx where
  isvar (PCType (PTVar n)) = Just (SubstName n)
  isvar _ = Nothing
--}

{--
instance PreUnifiable PCtx where
  walk s = do st <- get
              let go p@(PCType (PTMVar v)) | Just w <- getmvar v st = w
                                           | otherwise = p
                  go (PCType (PTVar n m)) = PCType (PTVar n (ignore (map go (unignore m))))
                  go p@(PCType (PTSym s)) = p
                  go (PCType (PTFun a b)) = PCType (PTFun (go a) (go b))
                  go (PCAll bnd) = let (name, val) = unsafeUnbind bnd
                                   in PCAll (bind name (go val))
                  go (PCRule c1 c2) = PCRule (go c1) (go c2)
              pure (go s)
  occurs i (PCType (PTVar _ m)) = any (occurs i) (unignore m)
  occurs i (PCType (PTMVar m)) = (i == m)
  occurs i (PCType (PTSym _)) = False
  occurs i (PCType (PTFun a b)) = occurs i a || occurs i b
  occurs i (PCAll bnd) = let (name, val) = unsafeUnbind bnd
                         in occurs i val
  occurs i (PCRule c1 c2) = occurs i c1 || occurs i c2

instance Reify PCtx PCtx where
  reify t = walk t

instance ScopedUnifiable PCtx where
  scopedUnify vars a b = undefined
--}


instance Alpha PTy
instance Alpha PCtx
instance Alpha PTm
{--


> joinContext :: PCtx (PCtx a) -> PCtx a
> joinContext (Type (Var x))      = x
> joinContext (Type TInt)         = Type TInt
> joinContext (Type (Fun p1 p2))  = Type (Fun (joinContext p1) (joinContext p2))
> joinContext (Rule p1 p2)        = Rule (joinContext p1) (joinContext p2)
> joinContext (Forall f)          = Forall (joinContext . f . Type . Var) 

System F (move to another file):

-- > data FExp v t = FVar v | FTVar t | Lam (v -> FExp v t) | Abs (t -> FExp v t) | App (

Type Checking 
>
> newtype Exp = E {unE :: forall a t . PExp t a}  

Inference

> inferExp :: Exp -> Maybe (PCtx Int)
> inferExp (E e) = infer [] e 0

> infer :: [PCtx Int] -> PExp Int (PCtx Int) -> Int -> Maybe (PCtx Int)
> infer env (EVar p1)    _ = return p1
> infer env (ELit x)     _ = return (Type TInt)
> infer env (ELam p1 f)  n = 
>   do p2 <- infer env (f p1) n
>      return (Type (Fun p1 p2))
> infer env (EApp e1 e2) n =
>   do (Type (Fun p1 p2)) <- infer env e1 n
>      p1' <- infer env e2 n
>      if (p1 ==  p1') then return p2 else fail ""
> infer env (ETLam f) n = 
>   do p <- infer env (f n) (n+1)
>      return (Forall (\a -> rename n a p))
> infer env (ETApp e1 p1) n = 
>   do (Forall f) <- infer env e1 n
>      return (subst n p1 (f n))
> infer env (EILam p1 e) n = 
>   do p2 <- infer (p1 : env) e n -- ambiguity check?
>      return (Rule p1 p2)
> infer env (EIApp e1 e2) n = 
>   do  (Rule p1 p2) <- infer env e1 n
>       p1' <- infer env e2 n
>       if (p1 == p1') then return p2 else fail ""
> infer env (EQuery p) n | tcResolve env p n = return p
> infer _ _ _ = Nothing

-- > fv :: Context Int -> Int -> [Int]
-- > fv (Type (Var z)) n      = [z]
-- > fv (Type TInt) n         = []
-- > fv (Type (Fun p1 p2)) n  = union (fv p1 n) (fv p2 n)
-- > fv (Forall f) n          = undefined

Substitution

> subst :: Int -> PCtx Int -> PCtx Int -> PCtx Int
> subst x p (Type (Var z)) 
>   | x == z = p
>   | otherwise = Type (Var z)
> subst x p (Type TInt)         = Type TInt
> subst x p (Type (Fun p1 p2))  = Type (Fun (subst x p p1) (subst x p p2))
> subst x p (Rule p1 p2)        = Rule (subst x p p1) (subst x p p2)
> subst x p (Forall f)          = Forall (subst x p . f)

Renaming

> rename :: Int -> Int -> PCtx Int -> PCtx Int
> rename x y (Type t)      = Type (renameType x y t)
> rename x y (Forall f)    = Forall (rename x y . f)
> rename x y (Rule p1 p2)  = Rule (rename x y p1) (rename x y p2)
>
> renameType :: Int -> Int -> PType Int -> PType Int
> renameType x y (Var z)
>   | x == z     = Var y
>   | otherwise  = Var z
> renameType x y TInt = TInt
> renameType x y (Fun p1 p2) = Fun (rename x y p1) (rename x y p2)

Resolution type checking

> tcResolve :: [PCtx Int] -> PCtx Int -> Int -> Bool
> tcResolve env (Forall f) n    = tcResolve env (f n) (n+1)
> tcResolve env (Rule p1 p2) n  = tcResolve (p1:env) p2 n 
> tcResolve env (Type t) n      = 
>   maybe False
>         (\(rs,n') -> all (\t -> tcResolve env t n') rs) 
>         (matchesFirst env t n)

> matchesFirst :: [PCtx Int] -> PType Int -> Int -> Maybe ([PCtx Int], Int)
> matchesFirst env t n = msum [matches r t n | r <- env]

> matches :: PCtx Int -> PType Int -> Int -> Maybe ([PCtx Int], Int)
> matches r t n = go r n [] []
>  where 
>   go (Type t')     n vars recs  = 
>     do subst <- unify t' t n vars
>        return (map (apply subst) recs, n)
>   go (Forall f)    n vars recs  = go (f n) (n + 1) (n : vars) recs
>   go (Rule ctxt r) n vars recs  = go r n vars (ctxt:recs)

> apply :: [(Int,PCtx Int)] -> PCtx Int -> PCtx Int
> apply subst r = gor r where
>   gor (Type t)      = got t
>   gor (Forall f)    = Forall (gor . f)
>   gor (Rule r1 r2)  = Rule (gor r1) (gor r2)


data SrcType t =
  STVar t
  | STInt
  | STFun (SrcType t) (SrcType t)
  | STIface String [SrcType t]

data SrcScheme t = Scheme [t] [SrcScheme t] (SrcType t)
  
showSrcType :: SrcType String -> String
showSrcType (STVar var) = var
showSrcType STInt = "Int"
showSrcType (STFun a b) = "(" ++ showSrcType a ++ ") -> " ++
                          showSrcType b
showSrcType (STIface iface types) =
  iface ++ " " ++ (intercalate " " (map showSrcType types))

lift :: SrcType a -> SrcScheme a
lift srctype = Scheme [] [] srctype

showSrcScheme :: SrcScheme String -> String
showSrcScheme (Scheme tvars schemes srctype) =
  (if null tvars then ""
   else "forall " ++ intercalate "," tvars ++ ". ") ++
  (if null schemes then ""
   else "{" ++ intercalate "," (map showSrcScheme schemes) ++ "} => ") ++
  showSrcType srctype

instance Show (SrcType String) where
  show = showSrcType
  
instance Show (SrcScheme String) where
  show = showSrcScheme

data SrcInterface t e = Interface String [t] [(e, SrcType t)]

showSrcInterface :: SrcInterface String String -> String
showSrcInterface (Interface iface tvars decls) =
  "interface " ++ iface ++ " " ++ (intercalate " " tvars) ++ " = { " ++
  (intercalate "; " . map (\(u, t) -> u ++ ":" ++ showSrcType t)) decls ++
  " }"

showPgm (ifaces, exp) =
  "[Interfaces]\n" ++
    intercalate "\n" (map show ifaces) ++ "\n" ++
    "[Program]\n" ++
    show exp ++ "\n"

instance Show (SrcInterface String String) where
  show = showSrcInterface

data SrcExp t e =
  SEVar e
  | SELit Int
  | SELam e (Maybe (SrcType t)) (SrcExp t e)
  | SEApp (SrcExp t e) (SrcExp t e)
  | SELVar (Maybe (SrcType t)) e
  | SEField (Maybe (SrcType t)) e
  | SELet e (SrcScheme t) (SrcExp t e) (SrcExp t e)
  | SEImplicit [e] (SrcExp t e)
  | SEQuery (Maybe (SrcType t))
  -- | SEAnnot (SrcExp t e) (SrcScheme t)
  | SEImpl String [(e, SrcExp t e)] (Maybe (SrcType t))

showSrcExp :: SrcExp String String -> String
showSrcExp (SELit n) = show n
showSrcExp (SEVar var) = var
showSrcExp (SELam binder Nothing body) =
  "\\" ++ binder ++ ". " ++ showSrcExp body
showSrcExp (SELam binder (Just ty) body) =
  "\\" ++ binder ++ ":" ++ showSrcType ty ++
  ". " ++ showSrcExp body
showSrcExp (SEApp a b) = "(" ++ showSrcExp a ++ ") " ++
                         showSrcExp b
showSrcExp (SELVar (Just ty) lvar) = lvar ++ " : " ++ showSrcType ty
showSrcExp (SELVar Nothing lvar) = lvar
showSrcExp (SEField (Just ty) field) = "\"" ++ field ++ "\" : " ++ showSrcType ty
showSrcExp (SEField Nothing field) = "\"" ++ field ++ "\""
showSrcExp (SELet lvar scheme e1 e2) =
  "let " ++ lvar ++ ": " ++ showSrcScheme scheme ++ " = " ++
  showSrcExp e1 ++ " in " ++ showSrcExp e2
showSrcExp (SEImplicit lvars body) =
  "implicit {" ++ intercalate "," lvars ++ "} in " ++
  showSrcExp body
showSrcExp (SEQuery Nothing) = "?"
showSrcExp (SEQuery (Just ty)) = "?[" ++ showSrcType ty ++ "]"
-- showSrcExp (SEAnnot body scheme) =
--   "(" ++ showSrcExp body ++ " : " ++ showSrcScheme scheme ++ ")"
showSrcExp (SEImpl iface defs ty) =
  iface ++ " {" ++ 
  (intercalate ", " . map (\(u, e) -> u ++ " = " ++ showSrcExp e)) defs ++
  "}" ++ (case ty of Just ty -> " : " ++ showSrcType ty
                     Nothing -> "")

instance Show (SrcExp String String) where
  show = showSrcExp

transformVarToLVar :: Ord e => SrcExp t e -> SrcExp t e
transformVarToLVar = transform empty
  where
    transform :: Ord e => Set e -> SrcExp t e -> SrcExp t e
    transform lvars (SEVar v) | v `member` lvars = SELVar Nothing v
    transform lvars (SELam binder ty body) =
      SELam binder ty $ transform (binder `delete` lvars) body
    transform lvars (SEApp a b) =
      SEApp (transform lvars a) (transform lvars b)
    transform lvars (SELet lvar scheme e1 e2) =
      SELet lvar scheme (transform lvars e1) (transform (lvar `insert` lvars) e2)
    transform lvars (SEImplicit vars body) =
      SEImplicit vars (transform lvars body)
--    transform lvars (SEAnnot exp scheme) = SEAnnot (transform lvars exp) scheme
    transform lvars (SEImpl iface defs ty) =
      SEImpl iface (map (second $ transform lvars) defs) ty
    transform lvars e = e
  
transformLVarToField :: Ord e => Set e -> SrcExp t e -> SrcExp t e
transformLVarToField fields = transform fields
  where
    transform :: Ord e => Set e -> SrcExp t e -> SrcExp t e
    transform fields (SEVar v) | v `member` fields = SEField Nothing v
    transform fields (SELVar ty v) | v `member` fields = SEField ty v
    transform fields (SELam binder ty body) =
      SELam binder ty $ transform (binder `delete` fields) body
    transform fields (SEApp a b) =
      SEApp (transform fields a) (transform fields b)
    transform fields (SELet lvar scheme e1 e2) =
      SELet lvar scheme (transform fields e1) (transform (lvar `delete` fields) e2)
    transform fields (SEImplicit vars body) =
      SEImplicit vars (transform fields body)
--    transform fields (SEAnnot exp scheme) = SEAnnot (transform fields exp) scheme
    transform fields (SEImpl iface defs ty) =
      SEImpl iface (map (second $ transform fields) defs) ty
    transform fields e = e
--}
--}
