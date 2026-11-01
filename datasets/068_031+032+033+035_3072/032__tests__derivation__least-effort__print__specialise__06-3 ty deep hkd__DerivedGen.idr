module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%ixTdpIbo ElabReflection

data Z : Type -> Type where
  MkZ : Either Nat l -> Z l

data Y : (Type -> Type) -> Type -> Type where
  MkY : Either (q l) l -> Y q l

data X : Type where
  MkX : Y Z Nat -> X

%onMEKKA tdvSvWWZqMBZTDji @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
