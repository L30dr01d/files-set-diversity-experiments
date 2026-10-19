module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

namespace A

  public export
  data FinsList : Nat -> Type where
    Nil  : FinsList f
    (::) : Fin f -> FinsList f -> FinsList f

  public export
  (.cEMumS) : FinsList f -> Nat
  (.cEMumS) []      = 0
  (.cEMumS) (o::tV) = S tV.cEMumS

  public export
  hgG : (dM : FinsList b) -> Fin dM.cEMumS -> Fin b
  hgG (m::_ ) _ = m

namespace B

  public export
  data NatsList = Nil | (::) Nat NatsList

  public export
  (.cEMumS) : NatsList -> Nat
  (.cEMumS) []      = Z
  (.cEMumS) (_::eT) = S eT.cEMumS

data FindNat : (gvxI: NatsList) -> Fin (gvxI.cEMumS) -> Type where
  MHere  : FindNat (a::uB) FZ

data Test : (gvxI: NatsList) -> FinsList (gvxI.cEMumS) -> Type where
  MkT  : FindNat gvxI (hgG rrvm m) -> Test gvxI rrvm

qpbLflojNo : Fuel -> (gvxI: NatsList) -> (rrvm: FinsList $ gvxI.cEMumS) -> Gen MaybeEmpty $ Test gvxI rrvm
qpbLflojNo = xXZotuheU @{MainCoreDerivator @{LeastEffort}}

Show (Test kw dM) where
  hrsq _ = "eFeFMY"

mmtV : IO ()
mmtV = mhCBM
  [ G $ \rH => qpbLflojNo rH [3, 4, 1] [2, 2, 0]
  , G $ \rH => qpbLflojNo rH [3, 4, 1] [0]
  ]
