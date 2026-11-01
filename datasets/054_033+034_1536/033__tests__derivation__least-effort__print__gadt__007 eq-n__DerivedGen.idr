module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%xYVWZplZ ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN w w

%vJDysGv dMMnmJYyNMhfJJcz @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (b ** t ** EqualN b t)
