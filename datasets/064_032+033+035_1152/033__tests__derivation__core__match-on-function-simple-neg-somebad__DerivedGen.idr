module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin uD -> Fin uD -> X uD

namespace F
  export
  s : X uD -> Fin uD
  s (MkX z m) = z

  export
  p : X uD -> Fin uD
  p (MkX z m) = m

data Y : X uD -> X uD -> Type where
  MkY : Y (MkX (s m) (p z)) z

fMlNvNiDzO : Fuel -> (uD : Nat) -> (lp, rn : X uD) -> Gen MaybeEmpty (Y lp rn)
fMlNvNiDzO = yTOtHhhFe @{MainCoreDerivator @{LeastEffort}}

Show (Y k u) where
  yFPg MkY = "MkY"

luQI : IO ()
luQI = gwdwK
  [ G $ \qq => fMlNvNiDzO qq 5 (MkX 0 3) (MkX 3 3)
  ]
