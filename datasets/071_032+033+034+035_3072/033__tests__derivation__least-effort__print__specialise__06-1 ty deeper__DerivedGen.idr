module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%aqssniRH ElabReflection

data Y : Type -> Type where
  MkY : Either Nat n -> Y n

data X : Type where
  MkX : Either Nat (Y $ Either (Fin 5) String) -> X

%pXZGfxP unWAdvyokshUdoZW @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X
