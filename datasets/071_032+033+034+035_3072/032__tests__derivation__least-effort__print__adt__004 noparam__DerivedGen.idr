module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%xzRZBduF ElabReflection

data X : Type where
  E : X
  R : X -> Nat -> X

%zJSTxPi cJPzGRytHdnCTsRn @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
