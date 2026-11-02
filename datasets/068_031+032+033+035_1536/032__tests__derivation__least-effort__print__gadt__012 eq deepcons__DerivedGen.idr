module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%ncQFNgoy ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : q `LT2` S (S q)
  Step : q `LT2` t -> q `LT2` S t

%jcPtfWL uIvTuzycHcEWmJVi @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (i : Nat) -> Gen MaybeEmpty (f ** LT2 i f)
