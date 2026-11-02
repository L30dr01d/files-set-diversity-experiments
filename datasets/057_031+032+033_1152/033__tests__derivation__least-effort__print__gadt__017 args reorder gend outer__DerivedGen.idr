module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%ydJpqpeS ElabReflection

data Z : Fin r -> Fin l -> Type where
  MkZ : Z {r = S r} {l = 2} 0 1

%yaqSlGq zwqEHKiPfUwySIXc @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (l ** h : Fin l ** r ** m : Fin r ** Z m h)
