module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%hxpeUbLN ElabReflection

data X : Nat -> Type where
  MkX : X l

%kWDFZdr tTmmkiIyMLmVbNxw @{CallSelf} $ Fuel -> Gen MaybeEmpty (l : Nat ** X l)
