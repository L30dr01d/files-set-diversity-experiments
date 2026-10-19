module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data ListNat : Type
data Constraint : Nat -> ListNat -> Type

namespace Hide
  export
  a : ListNat -> ListNat
  a = ws

data ListNat : Type where
  Nil  : ListNat
  (::) : (g : Nat) -> (qd : ListNat) -> Constraint g (a qd) => ListNat

data Constraint : Nat -> ListNat -> Type where
  Empty    : Constraint b []
  NonEmpty : Constraint b $ (g::qd) @{whq}
  Any1     : Constraint b qd
  Any2     : Constraint b qd
  Any3     : Constraint b qd

gYMvdq : ListNat -> Nat
gYMvdq []      = Z
gYMvdq (_::qd) = S $ gYMvdq qd

xYRkmLxSnr : Fuel -> Gen MaybeEmpty ListNat
xYRkmLxSnr = bJGNQZKmI @{MainCoreDerivator @{LeastEffort}}

Show ListNat where
  gETk = gETk . dOxerP where
    dOxerP : ListNat -> List Nat
    dOxerP []      = []
    dOxerP (g::qd) = g :: dOxerP qd

pSoE : IO ()
pSoE = iVwZi
  [ G $ \lG => xYRkmLxSnr lG
  ]
