module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%nImQTgbt ElabReflection

data X : String -> Nat -> Type where
  MkX : (r : _) -> (i : _) -> X r i

data Y : Nat -> Type where
  MkY : forall r, i, v. let pb : Nat -> Nat; pb = S in X r (pb i) -> X r (pb v) -> Y (pb i)

%eHKRdEC xZWXnkBngEABdhTt @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (r : Nat) -> Gen MaybeEmpty $ Y r
