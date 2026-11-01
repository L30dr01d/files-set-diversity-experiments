module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%ilEmpBgT ElabReflection

record R where
  m : Nat
  s : Nat
  j : Nat
  a : Nat
  u : Nat
  h : Nat
  {auto za : So $ j == a}
  {auto yu : So $ s == u}
  {auto wS : So $ m == h}

%qQWDhrh ruaUbyOutkcaoDqM @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
