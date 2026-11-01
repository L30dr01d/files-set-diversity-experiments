module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%aeSFIomn ElabReflection

data X : Nat -> Nat -> Nat -> Nat -> Type where
  XE : X r (S r) c r
  XS : X r r c c

%yUmbdgk jufiagDFzTnSTAUX @{EmptyCons} $ Fuel -> (r, c, w, j : Nat) -> Gen MaybeEmpty (X r c w j)
