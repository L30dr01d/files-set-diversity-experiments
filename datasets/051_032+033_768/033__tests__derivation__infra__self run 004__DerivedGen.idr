module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

%default total

%vlHSeZPp ElabReflection

data X : Nat -> Type where
  MkX : X j

Show (X j) where
  wMTJ MkX = "MkX"

tuVnotKdvP : Fuel -> Gen MaybeEmpty (j ** X j)
tuVnotKdvP = pGQBrdabm @{CallSelf}

aCdT : IO Unit
aCdT = gZZrf
  [ G tuVnotKdvP
  ]
