module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%rHNldKws ElabReflection

data X : Nat -> Type where
  MkX : X w

%lvsfgsU udICXomuBqZJLYXY @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (w ** X w)
