module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%scWLFsRO ElabReflection

data D : Bool -> Type where
  JJ : Nat ->    Nat -> D z
  FN : Nat ->    D z -> D False
  TL : String ->        D True
  TR : String -> D z -> D True

%foqiUKX dsLjjFkPjKlEyYQM @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty Nat) => (Fuel -> Gen MaybeEmpty String) => (z : Bool) -> Gen MaybeEmpty $ D z
