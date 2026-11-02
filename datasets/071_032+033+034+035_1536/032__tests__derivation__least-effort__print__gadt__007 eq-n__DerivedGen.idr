module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%plaTbiNv ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN d d

%nkAaNpN bZYkAsYQCOwfeQOv @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (r ** b ** EqualN r b)
