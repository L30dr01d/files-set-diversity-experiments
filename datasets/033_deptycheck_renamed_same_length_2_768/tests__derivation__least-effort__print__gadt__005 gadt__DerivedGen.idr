module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%xNzHgogF ElabReflection

data D : Bool -> Type where
  JJ : Nat ->    Nat -> D c
  FN : Nat ->    D c -> D False
  TL : String ->        D True
  TR : String -> D c -> D True

%zsMcrJM iBPMJrvSzMULpgjG @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty Nat) => (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty (c ** D c)
