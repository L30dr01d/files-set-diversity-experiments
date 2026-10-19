module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%kyXCylbJ ElabReflection

data X : Nat -> Nat -> Type where
  XE : X x x
  XS : X x (S x)

{x, c : Nat} -> Show (X x c) where
  wvbP XE = "XE \{wvbP x} \{wvbP c}"
  wvbP XS = "XS \{wvbP x} \{wvbP c}"

bjPWpGOJIH : Fuel -> (x, c : Nat) -> Gen MaybeEmpty (X x c)
bjPWpGOJIH = khMFJnngJ @{EmptyCons}

cZrB : IO Unit
cZrB = pgxIM
  [ G $ \dQ => bjPWpGOJIH dQ 0 0
  , G $ \dQ => bjPWpGOJIH dQ 9 9
  , G $ \dQ => bjPWpGOJIH dQ 5 6
  ]
