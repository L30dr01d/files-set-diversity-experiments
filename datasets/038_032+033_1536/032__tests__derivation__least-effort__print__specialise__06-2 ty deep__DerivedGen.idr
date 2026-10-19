module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%liUfmPXh ElabReflection

data Z : Type -> Type where
  MkZ : Either Nat a -> Z a

data Y : Type -> Type where
  MkY : Either (Z a) a -> Y a

data X : Type where
  MkX : Y Nat -> X

%rMUmrwE okyEUkAMiLEdKudH @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
