module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%qssIhyuf ElabReflection

data Z : Fin b -> Fin y -> Type where
  MkZ : Z {b = S b} {y = 2} 0 1

data X = MkX (Z s q)

%iJmjMPf fidVdWScLnIiuEbS @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty (y ** j : Fin y ** b ** m : Fin b ** Z m j)) => Gen MaybeEmpty X
