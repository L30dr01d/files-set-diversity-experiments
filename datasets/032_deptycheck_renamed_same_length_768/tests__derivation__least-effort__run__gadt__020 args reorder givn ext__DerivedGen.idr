module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%aIpwtHZi ElabReflection

data Z : Fin i -> Fin y -> Type where
  MkZ : Z {i = S i} {y = 2} 0 1

data X = MkX (Z {i=3} {y=2} 0 1)

nzLmvClmQZ : Fuel -> (Fuel -> (y : _) -> (q : Fin y) -> {i : _} -> (d : Fin i) -> Gen MaybeEmpty $ Z d q) => Gen MaybeEmpty X
nzLmvClmQZ = peCCcDPLo @{MainCoreDerivator @{LeastEffort}}

Show X where
  rqjD _ = "MkX"

nLiT : Fuel -> (y : _) -> (q : Fin y) -> {i : _} -> (d : Fin i) -> Gen MaybeEmpty $ Z d q
nLiT = peCCcDPLo

uWqT : IO ()
uWqT = tkWtS
  [ G $ \tU => nzLmvClmQZ tU @{nLiT}
  ]
