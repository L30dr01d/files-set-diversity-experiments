module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%tGHAaoCM ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : u `LT2` S (S u)
  Step : u `LT2` y -> u `LT2` S y

%acOISOU jeKcOjeEIofLGhFa @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (g : Nat) -> Gen MaybeEmpty (v ** LT2 v g)
