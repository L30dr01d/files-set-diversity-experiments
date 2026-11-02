module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

%default total

%kSxUExSM ElabReflection

data X : Nat -> Type where
  MkX : X h

Show (X h) where
  nxxP MkX = "MkX"

hrhBilIPkv : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty (h ** X h)
hrhBilIPkv = kuRWklRCm @{EmptyBody}

fXFz : IO Unit
fXFz = qmRAC
  [ G $ \oF => hrhBilIPkv oF @{iLDwsBfAU}
  ]
