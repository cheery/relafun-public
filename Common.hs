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
import Wasm.Core
import Sub

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

getKind :: MKind -> Kind
getKind (MKind t) = t
getKind (MRow _) = KRow

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
  | Query
  | ILet Tm Tm
  | TmStruct [(String, Tm)]
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
  | PILet Ty PTm PTm
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

-- Erase the types, not sure why keeping them in this long.
yerase :: YTm -> YTm
yerase (YVar name) = YVar name
yerase (YLit i) = YLit i
yerase (YLet bnd) = YLet (bind (name, ty, Embed (yerase tm1)) (yerase tm2))
  where ((name, ty, Embed tm1), tm2) = unsafeUnbind bnd
yerase (YLams bnd) = if length ys == 0 then yerase body
                                       else YLams (bind ([],ys) (yerase body))
  where ((xs, ys), body) = unsafeUnbind bnd
yerase (YApps f xs ys) | length ys == 0 = yerase f
                       | otherwise = (YApps (yerase f) [] (map yerase ys))


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
-- TODO: Implement structs.
-- TODO: Implement instancing.
-- TODO: Implement ilet
-- TODO: Implement instantiation on callsite.
-- TODO: Implement type-guided generalization.
