module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%xTMPfeuw ElabReflection

data X : Nat -> Type where
  MkX : {d : _} -> X d

data Y : Type where
  MkY : {d : _} -> X (d * 2) -> Y

%bACbyeG rRiQAFGDVltbPNSq @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y
