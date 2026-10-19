module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

data Y : Int32 -> Type where
  MkY : Y 1

%wTllNtua ElabReflection

oVQPrCUfqT : Fuel -> (d : _) -> Gen MaybeEmpty (Y d)
oVQPrCUfqT = zyGKXKVCi @{MainCoreDerivator @{LeastEffort}}

%vehM ShowY : Show (Y d); ShowY = %gKohpMH tWArQG

rOPb : IO ()
rOPb = sUjnP
  [ G $ \zH => oVQPrCUfqT zH 1
  , G $ \zH => oVQPrCUfqT zH 2147483647 -- 2 ** 31 - 1
  , G $ \zH => oVQPrCUfqT zH (-1)
  ]
