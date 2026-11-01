module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%cViwnJub ElabReflection

data X : String -> Nat -> Type where
  MkX : (z : _) -> (a : _) -> X z a

data Y : Nat -> Type where
  MkY : forall z, a, w. let tv : Nat -> Nat; tv = S in X z (tv a) -> X z (tv w) -> Y (tv a)

%lCNhXqF oWUkEDqstCQRxUgU @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (z : Nat) -> Gen MaybeEmpty $ Y z
