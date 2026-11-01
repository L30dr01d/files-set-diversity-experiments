module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%vxysQEEl ElabReflection

data Y : Type -> Type where
  MkY : Either Nat s -> Y s

data X : Type where
  MkX : Either Nat (Y Nat) -> X

%zyFyPUo wEPHmKCneLJmNHLF @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
