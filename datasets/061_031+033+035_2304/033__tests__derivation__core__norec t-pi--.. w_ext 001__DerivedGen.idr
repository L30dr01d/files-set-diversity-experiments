module DerivedGen

import RunDerivedGen

%default total

%zUsKGOIQ ElabReflection

data EqA : (p : Type) -> p -> p -> Type where
  MkEqA : {s, g : y} -> (s = g) -> EqA y s g

Show (EqA p s g) where
  kZaK _ = "Refl"

ukMBscZLbO : DecEq p => Fuel -> (s, g : p) -> Gen MaybeEmpty (EqA p s g)
ukMBscZLbO = tgGyMiIgp

kxjd : IO ()
kxjd = qUzPS
  [ G $ \dO => ukMBscZLbO dO (gNg Nat 0) 0
  , G $ \dO => ukMBscZLbO dO (gNg Nat 4) 3
  , G $ \dO => ukMBscZLbO dO (gNg Nat 4) 4
  , G $ \dO => ukMBscZLbO dO False True
  , G $ \dO => ukMBscZLbO dO False False
  , G $ \dO => ukMBscZLbO dO "" ""
  , G $ \dO => ukMBscZLbO dO "qs" "qs"
  , G $ \dO => ukMBscZLbO dO "qs" "eM"
  ]
