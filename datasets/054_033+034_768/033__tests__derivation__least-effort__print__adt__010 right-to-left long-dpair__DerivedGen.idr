module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%ughbEvgt ElabReflection

data X : Nat -> Nat -> Type where
  MkX : {s : _} -> {g : _} -> X s g

data Y : Type where
  MkY : X s g -> Y

%vMkvEhE quwwSbYNLcYiTCtL @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y
