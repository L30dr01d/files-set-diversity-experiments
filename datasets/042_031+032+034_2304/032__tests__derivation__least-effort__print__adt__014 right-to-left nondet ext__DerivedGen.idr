module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%tgbbmkRh ElabReflection

data X : String -> Nat -> Type where
  MkX : (m : _) -> (q : _) -> X m q

data Y : Type where
  MkY : X m q -> X m n -> Y

%himqrmp lJLtsjULqABPnTbS @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty Y
