module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%tTUNfnZZ ElabReflection

record R where
  s : Nat
  q : Nat
  c : Nat
  i : Nat
  d : Nat
  g : Nat
  {auto mj : So $ c == i}

%yYcYgBS ivfsTgGQOXqJPCqZ @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
