module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin re -> X re

namespace F
  export
  r : X re -> Fin re
  r (MkX h) = h

data Y : X re -> X re -> Type where
  MkY : Y (MkX (r f)) h

rXGjSfpzvg : Fuel -> (re : Nat) -> (xD, vI : X re) -> Gen MaybeEmpty (Y xD vI)
rXGjSfpzvg = knDyaRSOd @{MainCoreDerivator @{LeastEffort}}

Show (Y j a) where
  tcrk MkY = "MkY"

gSNB : IO ()
gSNB = orMXZ
  [ G $ \es => rXGjSfpzvg es 5 (MkX 0) (MkX 3)
  ]
