module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%jBDcZgCJ ElabReflection

data Z : Fin g -> Fin p -> Type where
  MkZ : Z {g = S g} {p = 2} 0 1

%hFfKzPd gLbyvIkwVGuWtfdL @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (p : _) -> (d : Fin p) -> {g : _} -> (z : Fin g) -> Gen MaybeEmpty $ Z z d
