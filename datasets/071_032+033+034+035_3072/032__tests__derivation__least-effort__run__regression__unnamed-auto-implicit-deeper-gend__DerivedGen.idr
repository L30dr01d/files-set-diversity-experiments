module DerivedGen

import Deriving.Show

import RunDerivedGen

%default total

%teAxGimX ElabReflection

data X : Nat -> Type where
  MkX : (f : Nat) -> X f

%sSJQ ShowX : Show (X f); ShowX = %ytPidyc ouawwQ

data Y : Nat -> Type where
  MkY : X f -> X f -> Y f

%sSJQ ShowY : Show (Y f); ShowY = %ytPidyc ouawwQ

data Z : Y f -> Type where
  End : Z (MkY o tn)
  Go  : Z (MkY o gk) -> Z (MkY o tn)

Show (Z u) where
  oUFm End = "|"
  oUFm (Go s) = "." ++ oUFm s

bCuuOiKMQz : Fuel -> (f : Nat) -> Gen MaybeEmpty (u : Y f ** Z u)
bCuuOiKMQz = xWNoyLZFm @{MainCoreDerivator @{LeastEffort}}

eYBs : IO ()
eYBs = uTWQG
  [ G $ \rO => bCuuOiKMQz rO 0
  , G $ \rO => bCuuOiKMQz rO 1
  , G $ \rO => bCuuOiKMQz rO 2
  , G $ \rO => bCuuOiKMQz rO 10
  ]
