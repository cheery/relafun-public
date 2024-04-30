{-# LANGUAGE DataKinds,
             FunctionalDependencies,
             ConstraintKinds,
             DefaultSignatures #-}
module Lib.Unify where

import Lib.ContEff hiding (Context)
import Lib.UnboundEff (Fresh', freshEff)
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)
import GHC.Generics
import Data.Typeable (Typeable)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Dynamic
import Data.Kind (Type)

type Unify = State UnifyState
type UnifyState = (M.Map Int Dynamic, M.Map Int Dynamic, Int)

newtype MVar (k :: Type) (s :: Type) = MVar Int
               deriving (Show, Ord, Eq, Generic, Typeable)
instance Alpha a => Alpha (MVar k a)
instance Subst t a => Subst t (MVar k a)

-- meant for parsing where it's inconvenient to create metavariables.
-- we can instead add holes and instantiate metavars later!
holeMVar :: forall k s. MVar k s
holeMVar = MVar (-1)

initUnify :: UnifyState
initUnify = (M.empty, M.empty, 0)

freshMeta :: forall k s eff. (Typeable k, Unify :< eff) => k -> Eff eff (MVar k s)
freshMeta k = do (q,m,c) <- get @UnifyState
                 put @UnifyState (M.insert c (toDyn k) q, m, c+1)
                 pure (MVar c)

getMeta' :: forall k s. (Typeable k) => MVar k s -> UnifyState -> k
getMeta' (MVar i) (q,_,_) = case M.lookup i q >>= fromDynamic of
                                Nothing -> error "inconsistent use of unification library"
                                Just a -> a

getMeta :: forall k s eff. (Typeable k, Unify :< eff) => MVar k s -> Eff eff k
getMeta i = get @UnifyState >>= (pure . getMeta' i)

getValue' :: forall k s. (Typeable s) => MVar k s -> UnifyState -> Maybe s
getValue' (MVar i) (_,m,_) = (M.lookup i m >>= fromDynamic)

getValue :: forall k s eff. (Typeable s, Unify :< eff) => MVar k s -> Eff eff (Maybe s)
getValue i = get @UnifyState >>= (pure . getValue' i)

runUnify :: forall a eff. UnifyState
         -> Eff (Unify ': eff) a -> Eff eff (UnifyState, a)
runUnify = state @UnifyState

tryUnify :: forall a eff. (Unify :< eff)
         => Eff (Unify ': Abort ': eff) a -> Eff eff (Maybe a)
tryUnify action = do st <- get @UnifyState
                     result <- try (runUnify st action)
                     case result of
                       Just (st', x) -> put st' >> pure (Just x)
                       Nothing       -> pure Nothing

occurs :: forall k t s. (Typeable k, Typeable t, Unifiable s) => MVar k t -> s -> Bool
occurs i = metafold go False
  where go :: Dynamic -> Bool -> Bool
        go dyn a | Just (j :: MVar k t) <- fromDynamic dyn = (i == j) || a
                 | otherwise = a

atomic :: Unifiable s => s -> Bool
atomic = metafold (\_ _ -> False) True

fmv :: (Typeable k, Typeable t, Unifiable s) => s -> S.Set (MVar k t)
fmv = metafold go S.empty
  where go dyn l = case fromDynamic dyn of
                        Nothing -> l
                        Just x -> S.insert x l

fv' :: (Alpha p, Typeable b) => p -> S.Set (Name b)
fv' x = S.fromList . toListOf fv $ x

(===) :: forall s eff. (Unifiable s, UAContext eff)
      => s -> s -> Eff eff ()
(===) x y = do x' <- walk x
               y' <- walk y
               autounify x' y'
               pure ()

ext :: forall k s eff. (Typeable k, Typeable s, Unifiable s, UAContext eff) => MVar k s -> s -> Eff eff ()
ext i@(MVar i') v | occurs i v = abort
                  | otherwise  = modify @UnifyState insertion
  where insertion (n,m,c) = (n,M.insert i' (toDyn v) m,c)

type UContext eff = (Fresh' :< eff, Unify :< eff)
type UAContext eff = (Fresh' :< eff, Unify :< eff, Abort :< eff)

class Unifiable s where
  unify :: (UAContext eff) => s -> s -> Maybe (Eff eff [Dynamic])
  unify _ _ = Nothing
  walklocal :: (UContext eff) => s -> Maybe (Eff eff s)
  walklocal _ = Nothing
  walk :: (UContext eff) => s -> Eff eff s
  default walk :: (Generic s, GUnifiable (Rep s), UContext eff)
                    => s -> Eff eff s
  walk u | Just action <- walklocal u = action
         | otherwise                  = to <$> gwalk (from u)
  metafold :: (Dynamic -> a -> a) -> a -> s -> a
  default metafold :: (Generic s, GUnifiable (Rep s))
                   => (Dynamic -> a -> a) -> a -> s -> a
  metafold f c u = gmetafold f c (from u)
  autounify :: (UAContext eff) => s -> s -> Eff eff [Dynamic]
  default autounify :: (Generic s, GUnifiable (Rep s), UAContext eff)
                    => s -> s -> Eff eff [Dynamic]
  autounify x y = case unify x y of
                    Just action -> action
                    Nothing -> gunify (from x) (from y)

class GUnifiable s where
  gwalk :: (UContext eff) => s c -> Eff eff (s c)
  gmetafold :: (Dynamic -> a -> a) -> a -> s c -> a
  gunify :: (UAContext eff) => s c -> s c -> Eff eff [Dynamic]

instance GUnifiable U1 where
  gwalk U1 = pure U1
  gmetafold _ a U1 = a
  gunify U1 U1 = pure []

instance (GUnifiable a, GUnifiable b) => GUnifiable (a :*: b) where
  gwalk (a :*: b) = (:*:) <$> gwalk a <*> gwalk b
  gmetafold f c (a :*: b) = gmetafold f (gmetafold f c b) a
  gunify (a :*: b) (c :*: d) = do st <- gunify a c
                                  b' <- gwalk b
                                  d' <- gwalk d
                                  st' <- gunify b' d'
                                  pure (st <> st')

instance (GUnifiable a, GUnifiable b) => GUnifiable (a :+: b) where
  gwalk (L1 x) = L1 <$> gwalk x
  gwalk (R1 x) = R1 <$> gwalk x
  gmetafold f a (L1 x) = gmetafold f a x
  gmetafold f a (R1 x) = gmetafold f a x
  gunify (L1 x) (L1 y) = gunify x y
  gunify (R1 x) (R1 y) = gunify x y
  gunify _ _ = abort

instance (GUnifiable a) => GUnifiable (M1 i c a) where
  gwalk (M1 x) = M1 <$> gwalk x
  gmetafold f a (M1 x) = gmetafold f a x
  gunify (M1 x) (M1 y) = gunify x y

instance Unifiable a => GUnifiable (K1 i a) where
  gwalk (K1 x) = K1 <$> walk x
  gmetafold f a (K1 x) = metafold f a x
  gunify (K1 x) (K1 y) = autounify x y

instance (Typeable k, Typeable t) => Unifiable (MVar k t) where
  metafold f a v = f (toDyn v) a

instance Unifiable (Name t) where
  walk s = pure s
  autounify x y | (x == y) = pure []
                | otherwise = abort
  metafold _ a _ = a

instance {-# OVERLAPPING #-} Unifiable String where
  walk s = pure s
  autounify x y | (x == y) = pure []
                | otherwise = abort
  metafold _ a _ = a
instance Unifiable a => Unifiable [a] where
  walk u = mapM walk u
  autounify [] [] = pure []
  autounify (x:xs) (y:ys) = do as <- autounify x y
                               bs <- autounify xs ys
                               pure (as <> bs)
  autounify a b = abort
  metafold f x ys = foldr (flip $ metafold f) x ys

instance Unifiable Char where
  walk s = pure s
  autounify x y | (x == y) = pure []
                | otherwise = abort
  metafold _ a _ = a

instance Unifiable Integer where
  walk s = pure s
  autounify x y | (x == y) = pure []
                | otherwise = abort
  metafold _ a _ = a

instance Unifiable Int where
  walk s = pure s
  autounify x y | (x == y) = pure []
                | otherwise = abort
  metafold _ a _ = a
