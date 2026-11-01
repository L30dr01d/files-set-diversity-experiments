module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%xyvqMJLj ElabReflection


public export
data Lookup : b -> List (b, c) -> Type where
  Here : (s : c) -> Lookup j $ (j, s)::pSX
  There : Lookup t pSX -> Lookup t $ (j, s)::pSX

data UseLookup : Type where
  UL : Lookup True [(True, True, True, True)] -> UseLookup

%yEulUzm aWmLiuVhuFHXfwGt @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty UseLookup
