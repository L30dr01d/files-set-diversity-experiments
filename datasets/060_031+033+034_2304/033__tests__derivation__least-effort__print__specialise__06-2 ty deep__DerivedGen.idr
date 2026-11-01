module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%wuOkXTVk ElabReflection

data Z : Type -> Type where
  MkZ : Either Nat t -> Z t

data Y : Type -> Type where
  MkY : Either (Z t) t -> Y t

data X : Type where
  MkX : Y Nat -> X

%abxHcUO aJxwmpFxGUkmOdTK @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
