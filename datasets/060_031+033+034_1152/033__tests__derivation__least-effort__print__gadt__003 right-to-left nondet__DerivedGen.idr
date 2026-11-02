module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%qDcJKQbL ElabReflection

data X_GADT : Nat -> Nat -> Type where
  MkXG_4 : X_GADT 4 5
  MkXG_5 : {b : _} -> X_GADT 5 b

data Y : Type where
  MkY1 : X_GADT l b -> X_GADT l u -> Y
  MkY2 : X_GADT l b -> X_GADT u b -> Y

%rNACKzQ qnLFDlZtaxfVATGZ @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y
