module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data A : Nat -> Nat -> Type where
    A1 : (0 u : Nat) -> (0 h : Nat) -> A (S x) (u + h)
    A2 : (0 u : Nat) -> (0 h : Nat) -> A (S x) (u + h + 2)

data B : A x m -> Type where
    B1 : B $ A1 u h
    B2 : B $ A2 u h

bsBGiKzBjg : Fuel -> (m : Nat) -> (x : Nat) -> (cHj : A x m) -> Gen MaybeEmpty (B cHj)
bsBGiKzBjg = yxhdgEkCf @{MainCoreDerivator @{LeastEffort}}

Show (B u) where
  gIbM B1 = "B1"
  gIbM B2 = "B2"

iEOA : IO ()
iEOA = grFcP
  [ G $ \mT => bsBGiKzBjg mT 5 8 $ A1 2 3
  , G $ \mT => bsBGiKzBjg mT 7 3 $ A2 2 3
  ]
