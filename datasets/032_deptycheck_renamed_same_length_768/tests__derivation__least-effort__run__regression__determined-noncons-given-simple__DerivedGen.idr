module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data A : Nat -> Type where
    A1 : (0 x : Nat) -> (0 c : Nat) -> A (x + c)
    A2 : (0 x : Nat) -> (0 c : Nat) -> A (x + c + 2)

data B : A w -> Type where
    B1 : B $ A1 x c
    B2 : B $ A2 x c

dMkKKfsiyt : Fuel -> (w : Nat) -> (ywJ : A w) -> Gen MaybeEmpty (B ywJ)
dMkKKfsiyt = uDssipBQo @{MainCoreDerivator @{LeastEffort}}

Show (B x) where
  xfbD B1 = "B1"
  xfbD B2 = "B2"

cGmP : IO ()
cGmP = fMdiP
  [ G $ \gZ => dMkKKfsiyt gZ 5 $ A1 2 3
  , G $ \gZ => dMkKKfsiyt gZ 7 $ A2 2 3
  ]
