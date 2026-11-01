module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%ovEHmmgn ElabReflection

data X : String -> Nat -> Type where
  MkX : (y : _) -> (b : _) -> X y b

data Y : Nat -> Type where
  MkY : forall y, b, z. let bC = S in X y (bC b) -> X y (bC z) -> Y (bC b)

%kAKghSK yxuHHouaOkPBoAyu @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (y : Nat) -> Gen MaybeEmpty $ Y y
