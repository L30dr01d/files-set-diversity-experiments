module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%dWmGbclA ElabReflection

record R where
  r : Nat
  v : Nat
  e : Nat
  f : Nat
  k : Nat
  s : Nat
  {auto bd : So $ e == f}
  {auto aR : So $ v == k}
  {auto lr : So $ r == s}

%uyGYwJT rNZCkawBsMvphFyg @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
