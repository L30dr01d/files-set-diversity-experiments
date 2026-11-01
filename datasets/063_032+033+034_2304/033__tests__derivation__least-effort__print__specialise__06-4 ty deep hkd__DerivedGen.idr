module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%qaOuLBwB ElabReflection

data Z : Type -> Type where
  MkZ : Either Nat v -> Z v

data Y : (Type -> Type) -> Type -> Type where
  MkY : Either (u v) (u $ u v) -> Y u v

data X : Type where
  MkX : Y Z Nat -> X

%aMdmDrX pyzjSABqBLECOyUJ @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
