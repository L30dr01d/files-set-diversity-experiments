module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%iXgINaVA ElabReflection

j : Nat -> Nat
j = (+2)

data Y : (x : Nat) -> Fin x -> Type where
  Y1 : Y 1 l
  Y2 : Y 2 1

data Z : Type where
  MkZ : (x : Nat) -> (o : Fin (j x)) -> (a : Y (j x) o) -> Z

%kagEQDL jMBeVoJdpPTZjJpC @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z
