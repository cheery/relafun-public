module Backend where

import Unbound.Generics.LocallyNameless
import GHC.Generics
import Data.Typeable (Typeable)
import qualified Data.Set as S
import Common
import Lib.Unify (fv')

-- STG directly from...
--   Making a Fast Curry: Push/Enter vs. Eval/Apply
--     for Higher-order Languages
--   Implementing lazy functional languages on stock hardware:
--     the Spineless Tagless G-machine
data Obj = Fun [Name Atom] (Bind [Name Atom] Expr)
         | Pap Atom [Atom]
         | Thunk [Name Atom] Expr
           deriving (Show, Generic, Typeable)
data Expr = Atom Atom
          | Apply Atom [Atom]
          | Let (Bind (Name Atom, Embed Obj) Expr)
          -- | LetRec (Bind (Rec [(Name Atom, Embed Obj)]) Expr)
           deriving (Show, Generic, Typeable)
data Atom = Var (Name Atom)
          | Lit31i Integer
           deriving (Show, Generic, Typeable)
type DebruijnIndex = Int

instance Alpha Obj
instance Alpha Expr
instance Alpha Atom

-- Helpful constructors for fun and thunk objects.
fun :: S.Set (Name Atom) -> (Bind [Name Atom] Expr) -> Obj
fun env bnd = Fun (S.toList (S.intersection env (fv' bnd))) bnd

thunk :: S.Set (Name Atom) -> Expr -> Obj
thunk env expr = Thunk (S.toList (S.intersection env (fv' expr))) expr
