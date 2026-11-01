module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%kHrbJUuW ElabReflection

data X : String -> Nat -> Type where
  MkX : (n : _) -> (z : _) -> X n z

data Y : Type where
  MkY : X n z -> X n k -> Y

%rgQaHVK xDtxpEiNBwQyerMD @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty Y
