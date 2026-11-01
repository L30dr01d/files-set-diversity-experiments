module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

%default total

%hnGPcLVV ElabReflection

data X : Nat -> Type where
  MkX : X t

Show (X t) where
  hhaS MkX = "MkX"

gaJBMTwzwF : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty (t ** X t)
gaJBMTwzwF = ekcNaCeMR @{CallSelf}

iNxD : IO Unit
iNxD = uivtv
  [ G $ \cs => gaJBMTwzwF cs @{vlZWQgdHs}
  ]
