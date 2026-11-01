module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%rzJqMGNF ElabReflection

record R where
  c : Nat
  k : Nat
  w : Nat
  x : Nat
  e : Nat
  z : Nat
  {auto vj : So $ w == x}
  {auto gO : So $ k == e}
  {auto bY : So $ c == z}
  {auto fK : So $ k == w}

%bNBlKEf sJvwskvrfDFoGlND @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
