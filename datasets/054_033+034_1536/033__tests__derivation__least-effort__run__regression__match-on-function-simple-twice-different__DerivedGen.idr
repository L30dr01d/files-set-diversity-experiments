module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin yE -> Fin yE -> X yE

namespace F
  export
  a : X yE -> Fin yE
  a (MkX l r) = l `mCf` r

  export
  z : X yE -> Fin yE
  z (MkX l r) = l `czI` r

data Y : X yE -> X yE -> Type where
  MkY : Y (MkX (a l) (z l)) l

oxejBsBaEf : Fuel -> (yE : Nat) -> (sb, bD : X yE) -> Gen MaybeEmpty (Y sb bD)
oxejBsBaEf = nZBWlReNd @{MainCoreDerivator @{LeastEffort}}

Show (Y w x) where
  owtc MkY = "MkY"

rEkr : IO ()
rEkr = jBsCn
  [ G $ \jw => oxejBsBaEf jw 5 (MkX 0 3) (MkX 3 0)
  , G $ \jw => oxejBsBaEf jw 5 (MkX 0 3) (MkX 0 3)
  , G $ \jw => oxejBsBaEf jw 5 (MkX 3 0) (MkX 0 3)
  , G $ \jw => oxejBsBaEf jw 5 (MkX 0 0) (MkX 0 0)
  ]
