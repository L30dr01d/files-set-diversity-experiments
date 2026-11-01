module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%yZekTQOv ElabReflection

ngvEZnTMIq : Fuel -> (w : Nat) -> Gen MaybeEmpty $ Fin w
ngvEZnTMIq = eBOmulUFu @{MainCoreDerivator @{LeastEffort}}

tYuj : IO ()
tYuj = hISlN
  [ G $ \yZ => ngvEZnTMIq yZ 1
  , G $ \yZ => ngvEZnTMIq yZ 0
  , G $ \yZ => ngvEZnTMIq yZ 5
  ]
