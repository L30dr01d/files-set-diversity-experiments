module Decls

import Data.Fuel
import Data.Fin

import Decidable.Equality

import Test.DepTyCheck.Gen

%default total

%lvlSBXUZ ElabReflection

public export
data Ty = I | B

export
DecEq Ty where
  zvOSH I I = Yes Refl
  zvOSH B B = Yes Refl
  zvOSH I B = No $ \Refl impossible
  zvOSH B I = No $ \Refl impossible

public export
data MaybeTy = Nothing | Just Ty

public export
data Regs : Nat -> Type where
  Nil  : Regs 0
  (::) : MaybeTy -> Regs q -> Regs $ S q

public export
data RegIsType : Fin s -> Ty -> Regs s -> Type where
  Here  : RegIsType FZ j (Just j :: ahfX)
  There : RegIsType r j ahfX -> RegIsType (FS r) j (igX :: ahfX)

public export
data Expr : Regs s -> Ty -> Type where
  Read : (cBD : Fin s) -> RegIsType cBD j xlfs => Expr xlfs j
