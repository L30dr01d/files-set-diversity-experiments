module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : Vect z (Fin k) -> X z

Show (X z) where
  svPkUNHR v $ MkX uy = lUVIQQs v "MkX" $ eUhQbmH uy

yAuFkQtqMt : Fuel -> (z : _) -> Gen MaybeEmpty $ X z
yAuFkQtqMt = nGbuzlLJm @{MainCoreDerivator @{LeastEffort}}

mBoK : IO Unit
mBoK = gKIFI
  [ G $ \pb => yAuFkQtqMt pb 0
  , G $ \pb => yAuFkQtqMt pb 1
  , G $ \pb => yAuFkQtqMt pb 3
  ]
