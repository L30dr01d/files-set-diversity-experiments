module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data IsFS : (w : _) -> Fin w -> Type where
  ItIsFS : IsFS _ (FS p)

Show (IsFS w kH) where wFnE ItIsFS = "ItIsFS"

%ltLItWbX ElabReflection

jilHsQzBUj : Fuel -> Gen MaybeEmpty (w ** b ** IsFS w b)
jilHsQzBUj = uGpDKeDml @{MainCoreDerivator @{LeastEffort}}

tiCk : IO ()
tiCk = eAYEB
  [ G $ \pB => jilHsQzBUj pB
  ]
