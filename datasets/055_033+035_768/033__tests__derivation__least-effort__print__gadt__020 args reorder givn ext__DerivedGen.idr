module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%yJYVcngd ElabReflection

data Z : Fin r -> Fin e -> Type where
  MkZ : Z {r = S r} {e = 2} 0 1

data X = MkX (Z {r=3} {e=2} 0 1)

%jUGUZlU omsXZFGzTcVpwqkT @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> (e : _) -> (p : Fin e) -> {r : _} -> (q : Fin r) -> Gen MaybeEmpty $ Z q p) => Gen MaybeEmpty X
