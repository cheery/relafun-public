{-# LANGUAGE
  BangPatterns,
  BlockArguments,
  DerivingStrategies,
  GADTs,
  GeneralizedNewtypeDeriving,
  MagicHash,
  UnboxedTuples,
  PolyKinds,
  DataKinds,
  FunctionalDependencies #-}
module Lib.ContEff where

import qualified Control.Exception as E
import Control.Exception.Base (NoMatchingContinuationPrompt(..))
import Data.Either
import Data.Foldable (for_)
import Data.Functor (void)
import Data.Functor.Sum (Sum(..))
import Data.Kind (Constraint, Type)
import Data.Maybe (fromMaybe, maybe, fromJust)
import System.IO.Unsafe
import System.Environment
import GHC.Exts (PromptTag#, newPromptTag#, prompt#, control0#)
import GHC.IO (IO(..))
import GHC.Stack (HasCallStack)
import Prelude hiding (log)
import qualified Data.Map as M
import qualified Data.Set as S

newtype Ctl a = Ctl (IO a)
  deriving newtype (Functor, Applicative, Monad)

data PromptTag a = PromptTag (PromptTag# a)

newPromptTag :: Ctl (PromptTag a)
newPromptTag = Ctl (IO f)
  where f s = case newPromptTag# s of
              (# s', tag #) -> (# s', PromptTag tag #)

prompt :: PromptTag a -> Ctl a -> Ctl a
prompt (PromptTag tag) (Ctl (IO m)) = Ctl (IO (prompt# tag m))

control0 :: PromptTag a -> ((Ctl b -> Ctl a) -> Ctl a) -> Ctl b
control0 (PromptTag tag) f = Ctl (IO (control0# tag g))
  where g k = case f (q k) of Ctl (IO b) -> b
        q k (Ctl (IO a)) = Ctl (IO (k a))

runCtl :: Ctl a -> Maybe a
runCtl (Ctl m) = unsafePerformIO
                 (E.catch (fmap Just m)
                          (\NoMatchingContinuationPrompt -> pure Nothing))

newtype Eff e a = Eff {unEff :: Context e -> Ctl a}

instance Functor (Eff e) where
  fmap f (Eff g) = Eff (fmap f . g)
instance Applicative (Eff e) where
  pure x = Eff (\_ -> pure x)
  Eff fc <*> Eff xc = Eff (\ctx -> fc ctx <*> xc ctx)
instance Monad (Eff e) where
  Eff m >>= f = Eff (\ctx -> do x <- m ctx
                                unEff (f x) ctx)

type (:<) :: (Type -> Type) -> [Type -> Type] -> Constraint
class op :< effs where
  perform :: (op a) -> Eff effs a

instance {-# OVERLAPPING #-} eff :< (eff : effs) where
  perform o = Eff (\(CCons tag _) -> control0 tag (pure . Op o))

instance (eff :< effs) => eff :< (eff' ': effs) where
  perform o = Eff (\(CCons _ ctx) -> unEff (perform @eff @effs o) ctx)

data Context e where
  CNil :: Context '[]
  CCons :: forall op ans eff.
           PromptTag (Com op ans)
           -> Context eff
           -> Context (op ': eff)

data Com op ans
  = Pure ans
  | forall arg. Op (op arg) (Ctl arg -> Ctl (Com op ans))

newtype Handler s e a = Handler {unHandle :: Eff e a}
  deriving newtype (Functor, Applicative, Monad)

type HandlerFunc op e a = forall c (s :: Type). (op c) -> (Eff e c -> Handler s e a) -> Handler s e a

handler :: Eff (op ': eff) a
        -> HandlerFunc op eff b
        -> (a -> Eff eff b)
        -> Eff eff b
handler (Eff action) h ret = do tag <- Eff (const newPromptTag)
                                ctx <- Eff pure
                                unHandle (hf tag (Pure `fmap` action (CCons tag ctx)))
    where hf tag action = do nxt <- Handler (Eff (const (prompt tag action)))
                             ctx <- Handler (Eff pure)
                             case nxt of
                               Op cmd cont -> h cmd (\arg -> hf tag (cont (unEff arg ctx)))
                               Pure a -> Handler (ret a)

data State s a where
  Get :: State s s
  Put :: s -> State s ()

get :: forall a eff. (State a :< eff) => Eff eff a
get = perform Get

put :: forall a eff. (State a :< eff) => a -> Eff eff ()
put x = perform (Put x)

modify :: forall a eff. (State a :< eff)
       => (a -> a) -> Eff eff ()
modify f = do st <- get
              put (f st)

state :: forall s a eff. s -> Eff (State s ': eff) a -> Eff eff (s, a)
state init (Eff action) = do tag <- Eff (const newPromptTag)
                             ctx <- Eff pure
                             hf tag (Pure `fmap` action (CCons tag ctx)) init
    where hf :: PromptTag (Com (State s) a) -> Ctl (Com (State s) a) -> s -> Eff eff (s, a)
          hf tag action st = do nxt <- Eff (const (prompt tag action))
                                case nxt of
                                  Op Get cont -> hf tag (cont (pure st)) st
                                  Op (Put st') cont -> hf tag (cont (pure ())) st'
                                  Pure a -> pure (st, a)

runEff :: Eff '[] a -> Maybe a
runEff e = runCtl (unEff e CNil)

runEff' :: Eff '[] a -> a
runEff' e = fromJust (runEff e)

-- a demo for writing
data Write s a where
  Write :: s -> Write s ()

write :: (Write s :< eff) => s -> Eff eff ()
write st = perform (Write st)

writeToList :: forall s a eff. Eff (Write s ': eff) a -> Eff eff (a, [s])
writeToList action = handler action fop fret
  where fop :: HandlerFunc (Write s) eff (a, [s])
        fop (Write x) cont = do (a, xs) <- cont (pure ())
                                pure (a, x:xs)
        fret a = pure (a, [])

-- asking for a demo
data Ask s a where
  Ask :: Ask s s

ask :: Ask s :< eff => Eff eff s
ask = perform Ask

give :: s -> (Eff (Ask s ': eff) a) -> Eff eff a
give s' action = handler action (fop s') fret
  where fop :: s -> HandlerFunc (Ask s) eff a
        fop st Ask cont = cont (pure st)
        fret a = pure a

data Abort a where
  Abort :: Abort a

abort :: forall a eff. (Abort :< eff) => Eff eff a
abort = perform Abort

try :: forall a eff. Eff (Abort ': eff) a -> Eff eff (Maybe a)
try action = handler action fop (pure . Just)
  where fop :: HandlerFunc Abort eff (Maybe a)
        fop Abort _ = pure Nothing

data Except t a where
  Except :: t -> Except t a

except :: forall t a eff. (Except t :< eff) => t -> Eff eff a
except e = perform (Except e)

catch :: forall t a eff. Eff (Except t ': eff) a -> Eff eff (Either t a)
catch action = handler action fop (pure . Right)
  where fop :: HandlerFunc (Except t) eff (Either t a)
        fop (Except e) _ = pure (Left e)
{--
type MVar = Int
type Unify s = State (UState s)
type UState s = (M.Map MVar s, MVar)

initUnify :: UState s
initUnify = (M.empty, 0)

class PreUnifiable s where
  walk :: (Unify s :< eff) => s -> Eff eff s
  occurs :: MVar -> s -> Bool

class PreUnifiable s => Unifiable s where
  unify :: (Unify s :< eff, Abort :< eff) => s -> s -> Eff eff ()

(===) :: (Unifiable s, Unify s :< eff, Abort :< eff) => s -> s -> Eff eff ()
(===) = unify

class PreUnifiable s => ScopedUnifiable s where
  scopedUnify :: (Unify s :< eff, Abort :< eff) => [s] -> s -> s -> Eff eff ()

raw :: forall t eff. (Unify t :< eff) => (MVar -> t) -> Eff eff t
raw f = do (s, c) <- get @(UState t)
           put (s, c+1)
           pure (f c)

getmvar :: MVar -> UState s -> Maybe s
getmvar m (s,c) = M.lookup m s

ext :: forall t eff. (PreUnifiable t, Unify t :< eff, Abort :< eff) => MVar -> t -> Eff eff ()
ext i v = do v' <- walk v
             if occurs i v'
             then do pure ()
             else do (s,c) <- get @(UState t)
                     put (M.insert i v s, c)

class Reify t v | t -> v where
  reify :: (Unify v :< eff) => t -> Eff eff t

class Free t v | t -> v where
  free :: t -> S.Set v
--}
