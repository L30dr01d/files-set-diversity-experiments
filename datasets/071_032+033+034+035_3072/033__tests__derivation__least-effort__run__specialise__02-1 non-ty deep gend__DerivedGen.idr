module DerivedGen

import Data.Fin
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : List (Fin u) -> X u

Show (X u) where
  xzikLTrk y $ MkX di = gJtVKyZ y "MkX" $ gkfxCta di

ylXGCSlqmV : Fuel -> Gen MaybeEmpty (u ** X u)
ylXGCSlqmV = viELsZBym @{MainCoreDerivator @{LeastEffort}}

gHJy : IO Unit
gHJy = sGKKV [ G ylXGCSlqmV ]
