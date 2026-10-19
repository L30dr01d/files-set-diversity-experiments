module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%nGCRcuND ElabReflection

data X : String -> Nat -> Type where
  MkX : (s : _) -> (k : _) -> X s k

data Y : Nat -> Type where
  MkY : (w : Nat) -> forall s, k, p. let jP = S in X s (jP k) -> X s (jP p) -> Y (jP w)

%inThZaY scHQtqehNYLTcoCy @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (s : Nat) -> Gen MaybeEmpty $ Y s
