module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%peHgoAqp ElabReflection

data X : Nat -> Type where
  MkX : {i : _} -> X i

data Y : Type where
  MkY : X i -> Y

%mhXPERN bYjNVhRKqxbihFUQ @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y
