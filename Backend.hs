module Backend where

import qualified Data.Set as S

-- STG directly from...
--   Making a Fast Curry: Push/Enter vs. Eval/Apply
--     for Higher-order Languages
--   Implementing lazy functional languages on stock hardware:
--     the Spineless Tagless G-machine
data Obj = Fun [DebruijnIndex] [Id] Expr
         | Pap Atom [Atom]
         | Thunk [DebruijnIndex] Expr
           deriving (Show)
data Expr = Atom Atom
          | Apply Atom [Atom]
          | Let [Bind] Expr
          | LetRec [Bind] Expr
           deriving (Show)
type Bind = (Id, Obj)
data Atom = Var DebruijnIndex
          | Sym Id
          | Lit31i Integer
           deriving (Show)
type Id = String
type DebruijnIndex = Int

-- Helpful constructors for fun and thunk objects.
fun :: [Id] -> Expr -> Obj
fun bd e = Fun (binders (length bd) (fvL e))
               bd e

thunk :: Expr -> Obj
thunk expr = Thunk (fvL expr) expr

-- Free variable computation
class FV a where
  fv :: a -> S.Set DebruijnIndex

instance FV Obj where
  fv (Fun free _ _) = S.fromList free
  fv (Pap f a) = fv f <> S.unions (map fv a)
  fv (Thunk free _) = S.fromList free

instance FV Expr where
  fv (Atom v) = fv v
  fv (Apply f a) = fv f <> S.unions (map fv a)
  fv (Let bd e) = fvlet (map snd bd) e
  fv (LetRec bd e) = bindersS (length bd) (fv e <> S.unions (map fv bd))

fvlet (x:xs) y = fv x <> bindersS 1 (fvlet xs y)
fvlet [] x = fv x

instance FV Bind where
  fv (_,o) = fv o

instance FV Atom where
  fv (Var i) = S.singleton i
  fv _ = S.empty

-- handling of Let/Letrec/Fun
binders :: Int -> [DebruijnIndex] -> [DebruijnIndex]
binders i = map (\x -> x - i) . filter (i<=)

fvL = S.toList . fv
bindersS i = S.fromList . binders i . S.toList

-- Demonstration
demo0 :: [Bind]
demo0 = [
  ("I", fun ["x"] (Atom$Var 0)),
  ("K", fun ["x", "y"] (Atom$Var 1)),
  ("S", fun ["x", "y", "z"]
            (Let [("", thunk (Apply (Var 1) [Var 0]))]
                 (Apply (Var 3) [Var 1, Var 0])))]
