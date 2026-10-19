module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

record FinInc u where
  constructor MkFinInc
  pEq : Nat
  cXY : LTE pEq u

%lntAQFLj ElabReflection

%kHUwZrf njkuOIZaLWwZFNLz @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (u ** FinInc u)
