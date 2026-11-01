module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data IsFS : Fin k -> Type where
  ItIsFS : IsFS (FS f)

Show (IsFS cg) where diRU ItIsFS = "ItIsFS"

%oUaIyHhx ElabReflection

ydWFwXBHiH : Fuel -> {k : Nat} -> (c : Fin k) -> Gen MaybeEmpty $ IsFS c
ydWFwXBHiH = eEwZoHsbq @{MainCoreDerivator @{LeastEffort}}

uQdt : IO ()
uQdt = wAePU
  [ G $ \ca => ydWFwXBHiH ca $ rVA (Fin 4) 3
  , G $ \ca => ydWFwXBHiH ca $ rVA (Fin 3) 0
  ]
