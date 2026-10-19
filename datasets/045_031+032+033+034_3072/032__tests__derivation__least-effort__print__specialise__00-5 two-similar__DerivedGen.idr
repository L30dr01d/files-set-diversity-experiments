module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%cjQXtNlX ElabReflection

data X = MkX (List String) (List Nat)

%czCquNb nVdhWBVmxMjQtwWm @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X
