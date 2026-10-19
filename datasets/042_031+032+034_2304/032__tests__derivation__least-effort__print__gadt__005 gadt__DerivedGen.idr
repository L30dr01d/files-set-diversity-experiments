module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%iVXEXcbq ElabReflection

data D : Bool -> Type where
  JJ : Nat ->    Nat -> D x
  FN : Nat ->    D x -> D False
  TL : String ->        D True
  TR : String -> D x -> D True

%lLpsZec smRcAifvwJodlxyl @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty Nat) => (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty (x ** D x)
