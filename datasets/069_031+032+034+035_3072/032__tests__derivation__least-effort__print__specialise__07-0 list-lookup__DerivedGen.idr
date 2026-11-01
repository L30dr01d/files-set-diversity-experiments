module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%tBmdkIlk ElabReflection


public export
data Lookup : f -> List (f, h) -> Type where
  Here : (o : h) -> Lookup x $ (x, o)::lHX
  There : Lookup a lHX -> Lookup a $ (x, o)::lHX

data UseLookup : Type where
  UL : Lookup True [(True, True, True, True)] -> UseLookup

%ljnkLom mRjjLRTcHldvsDOX @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty UseLookup
