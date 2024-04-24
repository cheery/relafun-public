module Inference where

import Lib.ContEff
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe)
import Syntax

type Fields = M.Map String Type
type Type = PType MVar

rmeta :: Type -> Maybe (Maybe MVar, Fields)
rmeta RClosed = Just (Nothing, M.empty)
rmeta (RMeta a i) = Just (Just i, M.fromList (map (,Con "Absent") (S.toList a)))
rmeta (RField n a b) | Just (k, m) <- rmeta b = Just (k, M.insert n a m)
rmeta _ = Nothing

instance Unifiable Type where
  fromMVar = Meta
  occurs i (Con n) = False
  occurs i (TApp a b) = occurs i a || occurs i b
  occurs i (Meta j) = (i == j)
  occurs i (RMeta _ j) = (i == j)
  occurs i (RField _ a b) = occurs i a || occurs i b
  occurs i RClosed = False
  walk t = do s <- get
              let go x@(Con n) = x
                  go (TApp a b) = TApp (go a) (go b)
                  go x@(Meta j) | Just y <- getmvar j s = go y
                                | otherwise            = x
                  go x@(RMeta a j) | Just y <- getmvar j s = go y
                                   | otherwise            = x
                  go (RField n a b) = RField n (go a) (go b)
                  go RClosed = RClosed
              pure (go t)
  unify t1 t2 = do t1' <- walk t1
                   t2' <- walk t2
                   go t1' t2'
    where go (Con x) (Con y) | x == y = pure ()
          go (TApp a b) (TApp c d) = (unify a c >> unify b d)
          go (Meta i) (Meta j) | i == j = pure ()
          go (Meta i) t2 = ext i t2
          go t1 (Meta j) = ext j t1
          go l r | Just (xi, aa) <- rmeta l, Just (xj, bb) <- rmeta r
            = do mapM id (M.intersectionWith unify aa bb)
                 top <- isClosed xi xj (S.fromList (M.keys (M.union aa bb)))
                 brush xi (M.toList $ M.difference bb aa) top
                 brush xj (M.toList $ M.difference aa bb) top
          go _ _ = abort
          brush Nothing [] top = pure ()
          brush (Just i) vec top = ext i (expand vec top)
          brush _ _ _ = abort
          expand [] top = top
          expand ((_, Con "Absent"):vs) top = expand vs top
          expand ((n, other):vs) top = RField n other (expand vs top)
          isClosed Nothing _       _ = pure RClosed
          isClosed _       Nothing _ = pure RClosed
          isClosed _       _       common = raw (RMeta common)

class Reify t where
  reify :: (Unify Type :< eff) => t -> Eff eff t

instance Reify Type where
  reify = walk

class Free t where
  free :: t -> S.Set MVar

instance Free Type where
  free (Con s) = S.empty
  free (TApp a b) = free a <> free b
  free (Meta i) = S.singleton i
  free (RMeta _ i) = S.singleton i
  free (RField _ a b) = free a <> free b
  free RClosed = S.empty

class Rename t where
  rename :: Subst Type -> t -> t

instance Rename Type where
  rename m x@(Con s) = x
  rename m (TApp a b) = TApp (rename m a) (rename m b)
  rename m x@(Meta i) = fromMaybe x (M.lookup i m)
  rename m x@(RMeta a i) = fromMaybe x (M.lookup i m)
  rename m (RField n a b) = RField n (rename m a) (rename m b)
  rename m RClosed = RClosed

data TypeScheme = TypeScheme (S.Set MVar) Type Constraints
  deriving (Show)

data VarContext = Mono String                               -- Monomorphic
                | Poly String TypeScheme -- Polymorphic

type Constraints = S.Set Constraint
data Constraint = CSi String Type -- Simple constraint
  deriving (Eq, Ord, Show)

instance Rename Constraint where
  rename r (CSi n t) = CSi n (rename r t)

instance Free Constraint where
  free :: Constraint -> S.Set MVar
  free (CSi _ t) = free t

instance Reify Constraint where
  reify (CSi n t) = fmap (CSi n) (reify t)

type VarMap = M.Map DeBruijnIndex Type
data Typing = Typing VarMap Type Constraints
              deriving (Show)

instance Reify Typing where
  reify (Typing v t c) = Typing
                      <$> mapM reify v
                      <*> reify t
                      <*> (fmap S.fromList $ mapM reify $ S.toList c)

nameOf :: VarContext -> String
nameOf (Mono n) = n
nameOf (Poly n _) = n

arrow :: Type -> Type -> Type
arrow a b = Con "->" `TApp` a `TApp` b

instantiate :: (Unify Type :< eff) => TypeScheme -> Eff eff (Type, Constraints)
instantiate (TypeScheme rs t c) = do
  r <- fmap M.fromList (mapM (\x -> fmap (x,) fresh) (S.toList rs))
  let t' = rename r t
  let c' = S.map (rename r) c
  pure (t', c')

infer :: (Write InferenceError :< eff, Unify Type :< eff)
      => M.Map String TypeScheme
      -> [VarContext]
      -> Term
      -> Eff eff Typing
infer g ctx (Var i) = case ctx !! i of
  Mono _ -> do t <- fresh
               pure (Typing (M.singleton i t) t S.empty)
  Poly _ s -> do (t, c) <- instantiate s
                 pure (Typing M.empty t c)
infer g ctx (Sym name) = case M.lookup name g of
  Just s -> do (t, c) <- instantiate s
               pure (Typing M.empty t c)
  Nothing -> do t <- fresh
                write (NotPresent name t)
                pure (Typing M.empty t S.empty)
infer g ctx (Lam name body) = do
  (Typing v t c) <- infer g (Mono name:ctx) body
  argtype <- case M.lookup 0 v of
                  Nothing -> fresh
                  Just t -> pure t
  let v' = M.mapKeys (\x -> x - 1) (M.delete 0 v)
  pure (Typing v' (arrow argtype t) c)
infer g ctx (App f x) = do
  Typing v1 ft c1 <- infer g ctx f
  Typing v2 xt c2 <- infer g ctx x
  restype <- fresh
  result <- tryUnify @Type $ do
    ft === arrow xt restype
    mapM_ id (M.intersectionWith (===) v1 v2)
    let v3 = M.union v1 v2
    pure (Typing v3 restype (c1 <> c2))
  case result of
    Nothing -> do write (WontApply (map nameOf ctx)
                                   f x
                                   (Typing v1 ft c1)
                                   (Typing v2 xt c2))
                  q <- fresh
                  pure (Typing M.empty q S.empty)
    Just typing -> pure typing
infer g ctx (Let name arg body) = do
  Typing v t c <- infer g ctx arg >>= reify
  let fv = S.unions (map (free . snd) (M.toList v))
  let vs = free t S.\\ fv
  let (c1, cg) = S.partition (\c -> S.null (free c `S.intersection` vs)) c
  let s = TypeScheme vs t c1
  Typing w q d <- infer g (Poly name s:ctx) body
  result <- tryUnify @Type $ do
    mapM_ id (M.intersectionWith (===) v w)
    pure (Typing (M.union v w) q (c <> d))
  case result of
    Nothing -> do write (WontLet (map nameOf ctx) arg body v w)
                  restype <- fresh
                  pure (Typing M.empty restype S.empty)
    Just t -> pure t
infer g ctx (Lit i) = do
  a <- fresh
  pure (Typing M.empty a (S.singleton (CSi "Num" a)))

type Names = [String]
data InferenceError = WontApply Names Term Term Typing Typing
                    | WontLet Names Term Term VarMap VarMap
                    | NotPresent String Type
                    deriving (Show)

instance Reify InferenceError where
  reify (WontApply names t v a b) = WontApply names t v <$> reify a <*> reify b
  reify (WontLet names x y a b) = WontLet names x y <$> mapM reify a <*> mapM reify b
  reify (NotPresent name a) = NotPresent name <$> reify a

{--
-- add an internal build system.
-- consider session types.
-- Think about the end result a bit.

mapLog :: (a -> b) -> Goal a c -> Goal b c
mapLog f (Goal g) = (Goal (fmap (third (map f)) . g))

tumbler :: String -> Goal InferenceError (Type, Constraints)
tumbler "map" = do
  a <- fresh
  b <- fresh
  f <- fresh
  let t = arrow (arrow a b) (arrow (f `TApp` a) (f `TApp` b))
  pure (t, S.singleton (CSi "Functor" f))
tumbler "+" = do
  a <- fresh
  let t = arrow a (arrow a a)
  pure (t, S.singleton (CSi "Arith" a))
tumbler n = do
  a <- fresh
  log' $ NotPresent n a
  pure (a, S.empty)
--}
