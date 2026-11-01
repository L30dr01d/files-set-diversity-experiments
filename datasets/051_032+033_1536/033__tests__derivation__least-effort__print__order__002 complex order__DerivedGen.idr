module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%hlJUsyuz ElabReflection

data BS : (r : Nat) -> Type where
  MkBS : BS r

p : Fin r -> BS r -> BS r
p k MkBS = MkBS

data X : (r : Nat) -> BS r -> Type where
  X0 : X 1 kZ
  X2 : X 3 kZ

data Y : (r : Nat) -> Fin r -> BS r -> Type where
  Y0 : Y 1 k kZ
  Y2 : Y 3 2 kZ

data Z : Type where
  MkZ : (r : Nat) -> (k : Fin r) -> (kZ : BS r) -> (u : X r (p k kZ)) -> (g : Y r k kZ) -> Z

%mzsANZq ghaGXPcNqxwwSNyJ @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z
