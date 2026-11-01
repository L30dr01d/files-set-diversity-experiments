module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%maSLDWkZ ElabReflection

data X : Bool -> Type where
  MkX : (s : Bool) -> X s

data Y : Bool -> Type where
  MkY : X s -> X s -> Y s

data Z : Y s -> Type where
  Start : Z m
  Go    : Z (MkY p tn) -> Z (MkY p dR)

%sVYCUqa bPetjhqfJFNDbVbQ $ Fuel -> (s : Bool) -> (m : Y s) -> Gen MaybeEmpty $ Z m
