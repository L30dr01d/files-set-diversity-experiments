module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%sYfPjalj ElabReflection

data X : String -> Nat -> Type where
  MkX : (n : _) -> (w : _) -> X n w

data Y : Nat -> Type where
  MkY : (t : Nat) -> forall n, w, l. X n (S w) -> X n (S l) -> let dF : Nat -> Nat; dF = S in Y (dF t)

%ibFjXAQ vYQTTOPxgaqJFvwE @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (n : Nat) -> Gen MaybeEmpty $ Y n
