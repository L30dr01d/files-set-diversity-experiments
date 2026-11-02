module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%qiczPEoF ElabReflection

data X : String -> Nat -> Type where
  MkX : (c : _) -> (v : _) -> X c v

data Y : Nat -> Type where
  MkY : (t : Nat) -> forall c, v, r. let mw = S in X c (mw v) -> X c (mw r) -> Y (mw t)

%tEFulZN yzkojwIiNvjQmgTp @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (c : Nat) -> Gen MaybeEmpty $ Y c
