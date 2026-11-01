module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data A : Nat -> Nat -> Type where
    A1 : (0 o : Nat) -> (0 i : Nat) -> A (S v) (o + i)
    A2 : (0 o : Nat) -> (0 i : Nat) -> A (S v) (o + i + 2)

data B : A v w -> Type where
    B1 : B $ A1 o i
    B2 : B $ A2 o i

potHJOQXyX : Fuel -> (w : Nat) -> (v : Nat) -> (tyF : A v w) -> Gen MaybeEmpty (B tyF)
potHJOQXyX = wLzQaDpMF @{MainCoreDerivator @{LeastEffort}}

Show (B o) where
  daYl B1 = "B1"
  daYl B2 = "B2"

kvyO : IO ()
kvyO = cZBjC
  [ G $ \oY => potHJOQXyX oY 5 8 $ A1 2 3
  , G $ \oY => potHJOQXyX oY 7 3 $ A2 2 3
  ]
