{-# LANGUAGE ImplicitParams #-}
module Inference where

import Lib.ContEff
import Lib.UnboundEff
import Unbound.Generics.LocallyNameless hiding (instantiate)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe)
import Lib.Unify
import Common
import Syntax
import Lib.Parser
import GHC.Generics
import Data.Typeable (Typeable)

-- Not certain whether this kind of coercive rule works.
(=|=) (MRow _) (MRow _) = pure ()
(=|=) (MRow _) (MKind t) = (t === KRow)
(=|=) (MKind t) (MRow _) = (t === KRow)
(=|=) (MKind t) (MKind u) = (t === u)

-- Remove type/kind holes in the expression.
tyMetaInst :: (Unify :< eff, Fresh' :< eff) => Ty -> Eff eff Ty
tyMetaInst (TVar name) = pure (TVar name)
tyMetaInst (TIdent name) = pure (TIdent name)
tyMetaInst (TMeta meta) | meta == holeMVar = do
  k <- KMeta <$> freshMeta ()
  t <- TMeta <$> freshMeta (MKind k)
  pure t
tyMetaInst (TMeta meta) = pure (TMeta meta)
tyMetaInst (TRField name ty row) = TRField name
                               <$> tyMetaInst ty
                               <*> tyMetaInst row
tyMetaInst TREnd = pure TREnd
tyMetaInst TFAbsent = pure TFAbsent
tyMetaInst (TFPresent tys) = TFPresent <$> mapM tyMetaInst tys
tyMetaInst (f :$: x) = (:$:) <$> tyMetaInst f <*> tyMetaInst x
tyMetaInst (TAll bnd) = do
  ((name, Embed mk), ty) <- unbind bnd
  mk' <- mkMetaInst mk
  ty' <- tyMetaInst ty
  pure (TAll (bind (name, Embed mk') ty'))
tyMetaInst (TRule a b) = TRule <$> tyMetaInst a <*> tyMetaInst b  

mkMetaInst :: (Unify :< eff, Fresh' :< eff) => MKind -> Eff eff MKind
mkMetaInst (MKind kind) = MKind <$> kindMetaInst kind
mkMetaInst (MRow a) = pure (MRow a)

kindMetaInst :: (Unify :< eff, Fresh' :< eff) => Kind -> Eff eff Kind
kindMetaInst (a :->: b) = (:->:) <$> kindMetaInst a <*> kindMetaInst b
kindMetaInst (KMeta meta) | meta == holeMVar = KMeta <$> freshMeta ()
kindMetaInst (KMeta meta) = pure (KMeta meta)
kindMetaInst KRow = pure KRow
kindMetaInst KField = pure KField
kindMetaInst KType = pure KType

assert bool | bool = pure ()
            | otherwise = abort

fromTry (Just a) = pure a
fromTry Nothing = abort

remove x [] = Nothing
remove x (y:ys) | x == y = Just ys
                | otherwise = (y:) <$> remove x ys

inferKind :: (Abort :< eff, Fresh' :< eff, Unify :< eff, ?kinds :: [(Ident, MKind)])
          => [(Name Ty, MKind)] -> Ty -> Eff eff MKind
inferKind env (TVar name) | Just k <- lookup name env = pure k
                          | otherwise = error $ "Kind lookup failed: " <> show name
inferKind env (TIdent (PId name)) | Just k <- lookup name ?kinds = pure k
                                  | otherwise = error $ "Kind lookup failed: " <> show name
inferKind env (TMeta meta) = getMeta meta
inferKind env (TRField label ty row) = do
  kr <- inferKind env row
  a <- case kr of
    MKind k -> (k === KRow) >> pure (MKind KRow)
    MRow absents -> MRow <$> fromTry (remove label absents)
  k <- inferKind env ty
  k =|= MKind KField
  pure a
inferKind env TREnd = pure (MKind KRow)
inferKind env TFAbsent = pure (MKind KField)
inferKind env (TFPresent tys) = do
  mapM_ (\ty -> inferKind env ty >>= (MKind KType =|=)) tys
  pure (MKind KField)
inferKind env (f :$: x) = do
  kf <- inferKind env f
  kx <- inferKind env x
  k <- KMeta <$> freshMeta ()
  a <- KMeta <$> freshMeta ()
  MKind a =|= kx
  kf =|= MKind (a :->: k)
  pure (MKind k)
inferKind env (TAll bnd) = do
  ((name, Embed kind), ty) <- unbind bnd
  inferKind ((name,kind):env) ty
inferKind env (TRule c d) = do
  kc <- inferKind env c
  kd <- inferKind env d
  MKind KType =|= kc
  MKind KType =|= kd
  pure (MKind KType)

type IEnv = M.Map (Name Tm) Var
data Var = Mono (Name PTm)    -- Monomorphic types go downwards.
         | Poly (Name PTm) Ty -- Polymorphic types go upwards.

-- Elaborated typing
data Typing = Typing VarMap Ty PTm
            deriving (Show, Generic, Typeable)

type VarMap = M.Map (Name PTm) Ty

data InferenceError = WontApply Tm Tm Typing Typing
                    | WontLet Tm Tm Typing Typing
                    | NotPresent (Name Tm) Ty
                    deriving (Show, Generic, Typeable)

arrow :: Ty -> Ty -> Ty
arrow a b = (TIdent (PId (s2n "→")) :$: a) :$: b

rename :: (Fresh' :< eff) => Name a -> Eff eff (Name b)
rename name = fresh (s2n (name2String name))

generalize :: (Unify :< eff, Fresh' :< eff) => Typing -> Eff eff Typing
generalize (Typing mh tyh tm) = do
  m <- mapM walk mh
  ty <- walk tyh
  let g = S.toList (fmv ty S.\\ S.unions (map (fmv.snd) (M.toList m)))
  (ty', tm') <- gen ty g
  pure (Typing m ty' tm')
  where gen :: (Unify :< eff, Fresh' :< eff)
            => Ty -> [MVar MKind Ty] -> Eff eff (Ty, PTm)
        gen ty [] = pure (ty, tm)
        gen ty (m:ms) = do (ty', tm') <- gen ty ms
                           mk <- getMeta m
                           name <- fresh (s2n "g")
                           _ <- try (ext m (TVar name))
                           ty'' <- walk ty'
                           tm'' <- walk tm'
                           let ty''' = TAll (bind (name, Embed mk) ty'')
                           let tm''' = PTLam (bind (name, Embed mk) tm'')
                           pure (ty''', tm''')

instantiate :: (Unify :< eff, Fresh' :< eff) => Ty -> PTm -> Eff eff Typing
instantiate (TAll bnd) tip = do
  ((name, Embed mkind), ty) <- unbind bnd
  meta <- TMeta <$> freshMeta mkind
  let ty' = subst name meta ty
  Typing vm ty'' tm <- instantiate ty' tip
  pure (Typing vm ty'' (PTApp tm meta))
instantiate (TRule c ty) tip = do
  Typing vm ty' tm <- instantiate ty tip
  pure (Typing vm ty' (PIApp tm (PQuery c)))
instantiate ty tip = do
  pure (Typing M.empty ty tip)

infer :: (Write InferenceError :< eff, Fresh' :< eff, Unify :< eff,
          ?typeMap :: M.Map Ident Var)
      => IEnv -> Tm -> Eff eff Typing
infer env (Ident (PId name)) | Just var <- M.lookup name ?typeMap
                             = case var of
                                 Mono name -> do ty <- TMeta <$> freshMeta (MKind KType)
                                                 pure (Typing (M.singleton name ty) ty (PVar name))
                                 Poly name ty -> instantiate ty (PVar name)
                             | otherwise
                             = do ty <- TMeta <$> freshMeta (MKind KType)
                                  write (NotPresent (s2n (name2String name)) ty)
                                  let tm = PVar (s2n (name2String name))
                                  pure (Typing M.empty ty tm)

infer env (Var name) | Just var <- M.lookup name env
                     = case var of
                         Mono name -> do ty <- TMeta <$> freshMeta (MKind KType)
                                         pure (Typing (M.singleton name ty) ty (PVar name))
                         Poly name ty -> instantiate ty (PVar name)
                     | otherwise
                     = do ty <- TMeta <$> freshMeta (MKind KType)
                          write (NotPresent name ty)
                          let tm = PVar (s2n (name2String name))
                          pure (Typing M.empty ty tm)
infer env (Lam bnd) = do
  (name, body) <- unbind bnd
  name' <- rename name
  let env' = (M.insert name (Mono name') env)
  Typing m ty tm <- infer env' body
  argtype <- case M.lookup name' m of
               Nothing -> TMeta <$> freshMeta (MKind KType)
               Just t -> pure t
  let m' = M.delete name' m
  tm' <- walk tm
  pure (Typing m' (arrow argtype ty) (PLam (bind (name', Embed argtype) tm')))
infer env (Let bnd) = do
  ((name, Embed arg), body) <- unbind bnd
  Typing m ty tm <- infer env arg >>= generalize
  name' <- rename name
  let env' = (M.insert name (Poly name' ty) env)
  Typing m' ty' tm' <- infer env' body

  cond <- tryUnify $ do
    mapM_ id (M.intersectionWith (===) m m')
  case cond of
    Just _ -> do tm'' <- walk tm'
                 let tm''' = PLet (bind (name', Embed ty, Embed tm) tm'')
                 pure (Typing (m <> m') ty' tm''')
    Nothing -> do write (WontLet arg body (Typing m ty tm)
                                          (Typing m' ty' tm'))
                  pure (Typing m' ty' tm')
infer env (App f x) = do
  Typing m ty tm <- infer env f
  Typing m' ty' tm' <- infer env x
  restype <- TMeta <$> freshMeta (MKind KType)
  cond <- tryUnify $ do
    ty === arrow ty' restype
    mapM_ id (M.intersectionWith (===) m m')
  case cond of
    Just _ -> do let tm'' = PApp tm tm'
                 pure (Typing (m <> m') restype tm'')
    Nothing -> do write (WontApply f x (Typing m ty tm) (Typing m' ty' tm'))
                  pure (Typing M.empty restype (PVar (s2n "_")))
infer env (Lit i) = do
  pure (Typing M.empty (TIdent (PId (s2n "integer"))) (PLit i))
