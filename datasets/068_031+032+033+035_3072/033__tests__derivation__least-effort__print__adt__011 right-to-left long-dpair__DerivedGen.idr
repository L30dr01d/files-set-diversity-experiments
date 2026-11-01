module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%eESGwpDy ElabReflection

data X : Nat -> Unit -> Type where
  MkX : {r : _} -> {m : _} -> X r m

data Y : Type where
  MkY : X r m -> Y

%qojkBYK utFwoPvnRZvnokqN @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y
