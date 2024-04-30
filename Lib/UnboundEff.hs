{-# LANGUAGE GADTs, UndecidableInstances, DataKinds #-}
module Lib.UnboundEff (Fresh', freshEff) where

import Lib.ContEff
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name (Name(Fn))

data Fresh' s where
  Fresh' :: (Name a) -> Fresh' (Name a)

instance (Fresh' :< eff) => Fresh (Eff eff) where
  fresh n = perform (Fresh' n)

freshEff :: forall a eff. Eff (Fresh' ': eff) a -> Eff eff a
freshEff (Eff action) = do tag <- Eff (const newPromptTag)
                           ctx <- Eff pure
                           hf tag (Pure `fmap` action (CCons tag ctx)) 0
    where hf :: PromptTag (Com Fresh' a) -> Ctl (Com Fresh' a) -> Integer -> Eff eff a
          hf tag action i = do nxt <- Eff (const (prompt tag action))
                               case nxt of
                                 Op (Fresh' (Fn n _)) cont -> hf tag (cont (pure (Fn n i))) (i+1)
                                 Pure a -> pure a
