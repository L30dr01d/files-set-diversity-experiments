module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

data X : Nat -> Nat -> Nat -> Type where
  MkX : X u u u

%bSmCQkQM ElabReflection

%mDLkkes zAIsdBLzBsWtIjaR @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (jV : Nat) -> (lE : Nat) -> (yW : Nat) -> Gen MaybeEmpty $ X jV lE yW
