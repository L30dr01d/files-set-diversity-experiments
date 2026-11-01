module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%klyjDmVU ElabReflection

data Z : Type -> Type where
  MkZ : Either Nat d -> Z d

data Y : (Type -> Type) -> Type -> Type where
  MkY : Either (n d) (n $ n d) -> Y n d

data X : Type where
  MkX : Y Z Nat -> X

%mQarMtI ytjGgsZgpjxNTINL @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
