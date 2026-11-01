module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%mTnuIolr ElabReflection

record R where
  k : Nat
  g : Nat
  n : Nat
  i : Nat
  c : Nat
  e : Nat
  {auto xD : So $ n == i}
  {auto we : So $ g == c}
  {auto iG : So $ k == e}
  {auto ch : So $ g == n}

%okDQRpR jCLPBlySgUTGcQyZ @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
