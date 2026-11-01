module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%vhfKUgVs ElabReflection

data X : Nat -> Nat -> Nat -> Nat -> Type where
  XE : X t (S t) p t
  XS : X t t p p

%gZEonLk ohpdsyQDlcJGXHia @{EmptyCons} $ Fuel -> (t, p, j, k : Nat) -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty (X t p j k)
