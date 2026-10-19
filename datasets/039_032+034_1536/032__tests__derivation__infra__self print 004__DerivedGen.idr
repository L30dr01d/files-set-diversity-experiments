module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%fFVoIkPT ElabReflection

data X : Nat -> Type where
  MkX : X h

%hLcIbZK fFuTetQeHTAgGMgV @{CallSelf} $ Fuel -> (h : Nat) -> Gen MaybeEmpty (X h)
