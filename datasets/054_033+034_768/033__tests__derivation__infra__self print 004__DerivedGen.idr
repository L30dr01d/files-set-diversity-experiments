module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%fRoEzrLM ElabReflection

data X : Nat -> Type where
  MkX : X t

%sgjqkjS cBObisrsMAQBsxkW @{CallSelf} $ Fuel -> (t : Nat) -> Gen MaybeEmpty (X t)
