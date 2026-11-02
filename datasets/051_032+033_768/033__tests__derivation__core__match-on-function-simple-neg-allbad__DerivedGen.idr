module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin iu -> X iu

namespace F
  export
  t : X iu -> Fin iu
  t (MkX w) = w

data Y : X iu -> X iu -> Type where
  MkY : Y (MkX (t x)) w

uGPOyGcFzC : Fuel -> (iu : Nat) -> (mr, sm : X iu) -> Gen MaybeEmpty (Y mr sm)
uGPOyGcFzC = pFEpNgjFh @{MainCoreDerivator @{LeastEffort}}

Show (Y j d) where
  mQjM MkY = "MkY"

qgRh : IO ()
qgRh = jgDEt
  [ G $ \zm => uGPOyGcFzC zm 5 (MkX 0) (MkX 3)
  ]
