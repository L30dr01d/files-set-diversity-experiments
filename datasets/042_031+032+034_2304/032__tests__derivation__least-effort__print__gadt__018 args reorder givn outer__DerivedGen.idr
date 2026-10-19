module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%fQBtQtrt ElabReflection

data Z : Fin a -> Fin n -> Type where
  MkZ : Z {a = S a} {n = 2} 0 1

%tQWzsQP yYrMPgoSnSIqUTKU @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (n : _) -> (g : Fin n) -> {a : _} -> (s : Fin a) -> Gen MaybeEmpty $ Z s g
