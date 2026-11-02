module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%fiAdCNXt ElabReflection

data X : String -> Nat -> Type where
  MkX : (u : _) -> (d : _) -> X u d

data Y : Nat -> Type where
  MkY : (l : Nat) -> forall u, d, n. let gL : Nat -> Nat; gL = S in X u (gL d) -> X u (gL n) -> Y (gL l)

%bHpSprR aSWxrivBHZyyCXUD @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (u : Nat) -> Gen MaybeEmpty $ Y u
