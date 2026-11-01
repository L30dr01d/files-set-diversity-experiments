module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%gufPqUGX ElabReflection

data Z : Type -> Type where
  MkZ : Either Nat v -> Z v

data Y : (Type -> Type) -> Type -> Type where
  MkY : Either (d v) v -> Y d v

data X : Type where
  MkX : Y Z Nat -> X

%phncuyp qbXcfsBetvFKfYhF @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
