module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin ng -> Fin ng -> X ng

namespace F
  export
  y : X ng -> Fin ng
  y (MkX o f) = o `obS` f

  export
  v : X ng -> X ng
  v (MkX o f) = MkX (o `jhG` f) (o `obS` f)

data Y : X ng -> X ng -> Type where
  MkY : Y (MkX (y o) (y $ v o)) o

bearaJIPXP : Fuel -> (ng : Nat) -> (aW, yu : X ng) -> Gen MaybeEmpty (Y aW yu)
bearaJIPXP = enOXmmOnZ @{MainCoreDerivator @{LeastEffort}}

Show (Y x i) where
  jMsN MkY = "MkY"

nWnq : IO ()
nWnq = qEcPX
  [ G $ \vf => bearaJIPXP vf 5 (MkX 0 3) (MkX 3 0)
  , G $ \vf => bearaJIPXP vf 5 (MkX 0 3) (MkX 0 3)
  , G $ \vf => bearaJIPXP vf 5 (MkX 3 0) (MkX 0 3)
  , G $ \vf => bearaJIPXP vf 5 (MkX 0 0) (MkX 0 0)
  ]
