module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data IsFS : (m : _) -> Fin m -> Type where
  ItIsFS : IsFS _ (FS q)

Show (IsFS m ag) where xKkz ItIsFS = "ItIsFS"

%sferJsYp ElabReflection

vsFWosNPjF : Fuel -> Gen MaybeEmpty (m ** d ** IsFS m d)
vsFWosNPjF = bvAwrqPrK @{MainCoreDerivator @{LeastEffort}}

yiEb : IO ()
yiEb = eamZU
  [ G $ \rM => vsFWosNPjF rM
  ]
