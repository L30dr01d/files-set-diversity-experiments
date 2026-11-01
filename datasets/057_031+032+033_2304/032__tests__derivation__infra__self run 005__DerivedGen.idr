module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

%default total

%jrSYcBvl ElabReflection

data X : Nat -> Type where
  MkX : X j

Show (X j) where
  frDm MkX = "MkX"

vMLyFacPrK : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty (j ** X j)
vMLyFacPrK = uubIVDIEt @{CallSelf}

rCMs : IO Unit
rCMs = oSpiI
  [ G $ \qA => vMLyFacPrK qA @{xEnUzhvwM}
  ]
