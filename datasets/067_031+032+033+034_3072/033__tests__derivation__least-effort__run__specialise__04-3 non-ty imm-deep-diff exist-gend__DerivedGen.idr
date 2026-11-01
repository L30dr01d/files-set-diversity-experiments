module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : Vect d (Fin c) -> X c

Show (X c) where
  neVBmycs o $ MkX sk = bZKbOfv o "MkX" $ rYZfPvy sk

edXcKkBRBj : Fuel -> Gen MaybeEmpty (c ** X c)
edXcKkBRBj = kGPAlPlod @{MainCoreDerivator @{LeastEffort}}

qZND : IO Unit
qZND = hCrYM [ G edXcKkBRBj ]
