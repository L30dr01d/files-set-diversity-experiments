module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%yAnEFATH ElabReflection

record R where
  i : Nat
  o : Nat
  y : Nat
  z : Nat
  c : Nat
  d : Nat
  {auto ts : So $ y == z}
  {auto dT : So $ o == c}
  {auto oY : So $ i == d}
  {auto nD : So $ o == y}
  {auto wl : So $ i == o}
  {auto jL : So $ i == 42}

%uEZZVUs kzQmoeidblYvnYPs @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
