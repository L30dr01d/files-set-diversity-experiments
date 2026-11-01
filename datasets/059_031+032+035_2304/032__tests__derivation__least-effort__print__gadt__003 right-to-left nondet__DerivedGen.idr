module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%xKpcRVxy ElabReflection

data X_GADT : Nat -> Nat -> Type where
  MkXG_4 : X_GADT 4 5
  MkXG_5 : {y : _} -> X_GADT 5 y

data Y : Type where
  MkY1 : X_GADT p y -> X_GADT p t -> Y
  MkY2 : X_GADT p y -> X_GADT t y -> Y

%sgowIun hvIjTvuKCiKqBWQC @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y
