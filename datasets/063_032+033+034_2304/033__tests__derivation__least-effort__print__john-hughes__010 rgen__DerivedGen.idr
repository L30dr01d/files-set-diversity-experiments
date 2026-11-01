module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%bdriZkKv ElabReflection

record R where
  c : Nat
  s : Nat
  a : Nat
  j : Nat
  d : Nat
  i : Nat
  {auto bp : So $ a == j}
  {auto hF : So $ s == d}
  {auto fb : So $ c == i}
  {auto xQ : So $ s == a}
  {auto rb : So $ c == s}
  {auto km : So $ i == 42}

%eYswBpa iziFdmPrOODTpKum @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
