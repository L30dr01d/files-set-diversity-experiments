module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

%default total

%qLeCUYfC ElabReflection

data X : Nat -> Type where
  MkX : X q

Show (X q) where
  hzZl MkX = "MkX"

nzSvmJWbwx : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty (q ** X q)
nzSvmJWbwx = uSyuKKHHB @{EmptyCons}

qDWl : IO Unit
qDWl = oQnbp
  [ G $ \jX => nzSvmJWbwx jX @{evMqusfFv}
  ]
