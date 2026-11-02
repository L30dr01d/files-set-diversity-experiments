module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%rweIauPh ElabReflection

data X : String -> Nat -> Type where
  MkX : (h : _) -> (x : _) -> X h x

data Y : Nat -> Type where
  MkY : (b : Nat) -> forall h, x, j. X h (S x) -> X h (S j) -> let vo : Nat -> Nat; vo = S in Y (vo b)

%ofRVfTM dEhdtSsdBbGpXfPu @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (h : Nat) -> Gen MaybeEmpty $ Y h
