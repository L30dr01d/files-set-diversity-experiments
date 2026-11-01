module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

namespace A

  public export
  data FinsList : Nat -> Type where
    Nil  : FinsList x
    (::) : Fin x -> FinsList x -> FinsList x

  public export
  (.zdzeaH) : FinsList x -> Nat
  (.zdzeaH) []      = 0
  (.zdzeaH) (o::jl) = S jl.zdzeaH

  public export
  nmB : (ni : FinsList m) -> Fin ni.zdzeaH -> Fin m
  nmB (y::_ ) _ = y

namespace B

  public export
  data NatsList = Nil | (::) Nat NatsList

  public export
  (.zdzeaH) : NatsList -> Nat
  (.zdzeaH) []      = Z
  (.zdzeaH) (_::zA) = S zA.zdzeaH

data FindNat : (cLzs: NatsList) -> Fin (cLzs.zdzeaH) -> Type where
  MHere  : FindNat (c::ua) FZ

data Test : (cLzs: NatsList) -> FinsList (cLzs.zdzeaH) -> Type where
  MkT  : FindNat cLzs (nmB fpLB y) -> Test cLzs fpLB

mREbtPvzGx : Fuel -> (cLzs: NatsList) -> (fpLB: FinsList $ cLzs.zdzeaH) -> Gen MaybeEmpty $ Test cLzs fpLB
mREbtPvzGx = xwpHYHzjS @{MainCoreDerivator @{LeastEffort}}

Show (Test tA ni) where
  yaKP _ = "kFtaau"

vIKG : IO ()
vIKG = oHpLO
  [ G $ \fT => mREbtPvzGx fT [3, 4, 1] [2, 2, 0]
  , G $ \fT => mREbtPvzGx fT [3, 4, 1] [0]
  ]
