module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%lTpatedj ElabReflection

j : Nat -> Nat
j = (+2)

data Y : (q : Nat) -> Fin q -> Type where
  Y1 : Y 1 s
  Y2 : Y 2 1

data Z : Type where
  MkZ : (q : Nat) -> (d : Fin (j q)) -> (n : Y (j q) d) -> Z

%sasVVzo jEcLNhYtdfubIIBV @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z
