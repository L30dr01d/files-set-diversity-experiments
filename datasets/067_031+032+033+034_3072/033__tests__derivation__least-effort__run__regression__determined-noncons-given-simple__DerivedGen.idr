module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data A : Nat -> Type where
    A1 : (0 j : Nat) -> (0 n : Nat) -> A (j + n)
    A2 : (0 j : Nat) -> (0 n : Nat) -> A (j + n + 2)

data B : A h -> Type where
    B1 : B $ A1 j n
    B2 : B $ A2 j n

iUqgTcmouS : Fuel -> (h : Nat) -> (kGl : A h) -> Gen MaybeEmpty (B kGl)
iUqgTcmouS = pfcehxGsI @{MainCoreDerivator @{LeastEffort}}

Show (B j) where
  ySaS B1 = "B1"
  ySaS B2 = "B2"

oMaG : IO ()
oMaG = lUPdh
  [ G $ \yx => iUqgTcmouS yx 5 $ A1 2 3
  , G $ \yx => iUqgTcmouS yx 7 $ A2 2 3
  ]
