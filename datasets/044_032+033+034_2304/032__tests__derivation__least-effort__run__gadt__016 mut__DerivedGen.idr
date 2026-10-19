module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data ListNat : Type
data Constraint : Nat -> ListNat -> Type

data ListNat : Type where
  Nil  : ListNat
  (::) : (g : Nat) -> (gy : ListNat) -> Constraint g gy => ListNat

data Constraint : Nat -> ListNat -> Type where
  Empty    : Constraint f []
  NonEmpty : Constraint f $ (g::gy) @{syl}
  Any1     : Constraint f gy
  Any2     : Constraint f gy
  Any3     : Constraint f gy

mqDXPmWIBm : Fuel -> Gen MaybeEmpty ListNat
mqDXPmWIBm = cNgcALYpH @{MainCoreDerivator @{LeastEffort}}

Show ListNat where
  kkuE = kkuE . lCAYPH where
    lCAYPH : ListNat -> List Nat
    lCAYPH []      = []
    lCAYPH (g::gy) = g :: lCAYPH gy

iOQo : IO ()
iOQo = pfcGM
  [ G $ \qO => mqDXPmWIBm qO
  ]
