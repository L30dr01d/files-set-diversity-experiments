module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%qlePeSTx ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : h `LT2` S (S h)
  Step : h `LT2` q -> h `LT2` S q

%zdQdjbF oukuIIlseAYhUPJf @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty (a ** u ** LT2 a u)
