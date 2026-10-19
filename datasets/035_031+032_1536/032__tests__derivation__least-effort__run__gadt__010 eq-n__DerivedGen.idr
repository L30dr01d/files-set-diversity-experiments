module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%tNyPvkik ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN a a

{p, m : Nat} -> Show (EqualN p m) where
  nGBb ReflN = "ReflN : EqualN \{nGBb p} \{nGBb m}"

sJkakEPVbD : Fuel -> (p, m : Nat) -> Gen MaybeEmpty $ EqualN p m
sJkakEPVbD = kwHNDZgHv @{MainCoreDerivator @{LeastEffort}}

dExz : IO ()
dExz = ihKVU
  [ G $ \cA => sJkakEPVbD cA 5 0
  , G $ \cA => sJkakEPVbD cA 5 5
  , G $ \cA => sJkakEPVbD cA 0 1
  , G $ \cA => sJkakEPVbD cA 0 0
  , G $ \cA => sJkakEPVbD cA 11 12
  , G $ \cA => sJkakEPVbD cA 12 12
  ]
