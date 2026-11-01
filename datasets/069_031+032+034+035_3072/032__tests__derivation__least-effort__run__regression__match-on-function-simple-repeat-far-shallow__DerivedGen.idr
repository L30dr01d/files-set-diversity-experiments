module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin zF -> X zF

namespace F
  export
  r : X zF -> Fin zF
  r (MkX o) = o

data Y : X zF -> X zF -> X zF -> Type where
  MkY : Y (MkX (r o)) (MkX (r o)) o

rtygWuDpPp : Fuel -> (zF : Nat) -> (es, jv, sd : X zF) -> Gen MaybeEmpty (Y es jv sd)
rtygWuDpPp = mAdxogpoT @{MainCoreDerivator @{LeastEffort}}

Show (Y k t f) where
  rAQd MkY = "MkY"

gyWU : IO ()
gyWU = jVkwE
  [ G $ \dx => rtygWuDpPp dx 5 (MkX 0) (MkX 0) (MkX 3)
  , G $ \dx => rtygWuDpPp dx 5 (MkX 0) (MkX 3) (MkX 3)
  , G $ \dx => rtygWuDpPp dx 5 (MkX 3) (MkX 0) (MkX 3)
  , G $ \dx => rtygWuDpPp dx 5 (MkX 0) (MkX 0) (MkX 0)
  ]
