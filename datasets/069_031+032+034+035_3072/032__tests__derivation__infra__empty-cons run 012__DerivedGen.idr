module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%rHwBFOaF ElabReflection

data X : Nat -> Nat -> Nat -> Nat -> Type where
  XE : X o (S o) d o
  XS : X o o d d

{o, d, f, i : Nat} -> Show (X o d f i) where
  xSXJ XE = "XE \{xSXJ o} \{xSXJ d} \{xSXJ f} \{xSXJ i}"
  xSXJ XS = "XS \{xSXJ o} \{xSXJ d} \{xSXJ f} \{xSXJ i}"

bVpKZadIvB : Fuel -> (o, d, f, i : Nat) -> Gen MaybeEmpty (X o d f i)
bVpKZadIvB = nVVUqZpNt @{EmptyCons}

sdgu : IO Unit
sdgu = iKfky
  [ G $ \zG => bVpKZadIvB zG 0 0 0 0
  , G $ \zG => bVpKZadIvB zG 8 9 7 7
  , G $ \zG => bVpKZadIvB zG 5 6 7 8
  ]
