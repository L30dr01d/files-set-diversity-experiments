module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

namespace A

  public export
  data FinsList : Nat -> Type where
    Nil  : FinsList p
    (::) : Fin p -> FinsList p -> FinsList p

  public export
  (.llylVC) : FinsList p -> Nat
  (.llylVC) []      = 0
  (.llylVC) (i::fA) = S fA.llylVC

  public export
  iZE : (iZ : FinsList d) -> Fin iZ.llylVC -> Fin d
  iZE (q::_ ) _ = q

namespace B

  public export
  data NatsList = Nil | (::) Nat NatsList

  public export
  (.llylVC) : NatsList -> Nat
  (.llylVC) []      = Z
  (.llylVC) (_::ns) = S ns.llylVC

data FindNat : (aMoA: NatsList) -> Fin (aMoA.llylVC) -> Type where
  MHere  : FindNat (z::zA) FZ

data Test : (aMoA: NatsList) -> FinsList (aMoA.llylVC) -> Type where
  MkT  : FindNat aMoA (iZE fnbC q) -> Test aMoA fnbC

%niXhaWnK ElabReflection

%mnimXdc cCGOKDIhKRmjdlJz @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (aMoA: NatsList) -> (fnbC: FinsList $ aMoA.llylVC) -> Gen MaybeEmpty $ Test aMoA fnbC
