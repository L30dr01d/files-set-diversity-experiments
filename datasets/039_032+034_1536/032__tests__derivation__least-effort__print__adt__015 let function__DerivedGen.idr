module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%yBoBtzVk ElabReflection

data X : String -> Nat -> Type where
  MkX : (d : _) -> (m : _) -> X d m

data Y : Nat -> Type where
  MkY : (w : Nat) -> forall d, m, k. let wp : Nat -> Nat; wp = S in X d (wp m) -> X d (wp k) -> Y (wp w)

%uiNgHVA ljNrAHphNVaOJtxt @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (d : Nat) -> Gen MaybeEmpty $ Y d
