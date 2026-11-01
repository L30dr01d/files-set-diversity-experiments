module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

record FinInc u where
  constructor MkFinInc
  wwU : Nat
  gik : LTE wwU u

%uRIsgRff ElabReflection

%cTifUzF zvRopLqSqOAbMkGo @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (u ** FinInc u)
