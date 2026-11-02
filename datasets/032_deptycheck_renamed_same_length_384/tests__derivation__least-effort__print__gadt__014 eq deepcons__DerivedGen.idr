module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%ojqkrmkX ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : n `LT2` S (S n)
  Step : n `LT2` o -> n `LT2` S o

%aKrpOqO aPQSDEszoUKbUexW @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (t, j : Nat) -> Gen MaybeEmpty $ LT2 t j
