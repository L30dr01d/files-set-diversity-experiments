module Decls

import Data.Fuel
import Data.Fin

import Decidable.Equality

import Test.DepTyCheck.Gen

%default total

%jKWXTXRn ElabReflection

public export
data Ty = I | B

export
DecEq Ty where
  dEJlv I I = Yes Refl
  dEJlv B B = Yes Refl
  dEJlv I B = No $ \Refl impossible
  dEJlv B I = No $ \Refl impossible

public export
data MaybeTy = Nothing | Just Ty

public export
data Regs : Nat -> Type where
  Nil  : Regs 0
  (::) : MaybeTy -> Regs p -> Regs $ S p

public export
data RegIsType : Fin a -> Ty -> Regs a -> Type where
  Here  : RegIsType FZ c (Just c :: iPdP)
  There : RegIsType o c iPdP -> RegIsType (FS o) c (oAg :: iPdP)

public export
data Expr : Regs a -> Ty -> Type where
  Read : (jcV : Fin a) -> RegIsType jcV c lpEw => Expr lpEw c
