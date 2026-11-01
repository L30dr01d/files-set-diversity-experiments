module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin uT -> X uT

namespace F
  export
  n : X uT -> Fin uT
  n (MkX w) = w

data Y : X uT -> X uT -> Type where
  MkY : Y (MkX (n w)) w

yrfsRKcFnu : Fuel -> (uT : Nat) -> (ic, gG : X uT) -> Gen MaybeEmpty (Y ic gG)
yrfsRKcFnu = kYkQfPEQN @{MainCoreDerivator @{LeastEffort}}

Show (Y p k) where
  wBMX MkY = "MkY"

zHcz : IO ()
zHcz = nhqGQ
  [ G $ \vt => yrfsRKcFnu vt 5 (MkX 0) (MkX 3)
  , G $ \vt => yrfsRKcFnu vt 5 (MkX 0) (MkX 0)
  ]
