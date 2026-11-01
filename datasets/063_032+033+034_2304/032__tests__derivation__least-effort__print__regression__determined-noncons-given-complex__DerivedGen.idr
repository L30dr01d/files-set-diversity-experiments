module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

namespace A

  public export
  data FinsList : Nat -> Type where
    Nil  : FinsList i
    (::) : Fin i -> FinsList i -> FinsList i

  public export
  (.zNnXiL) : FinsList i -> Nat
  (.zNnXiL) []      = 0
  (.zNnXiL) (y::dz) = S dz.zNnXiL

  public export
  pEb : (gc : FinsList s) -> Fin gc.zNnXiL -> Fin s
  pEb (j::_ ) _ = j

namespace B

  public export
  data NatsList = Nil | (::) Nat NatsList

  public export
  (.zNnXiL) : NatsList -> Nat
  (.zNnXiL) []      = Z
  (.zNnXiL) (_::pN) = S pN.zNnXiL

data FindNat : (odaC: NatsList) -> Fin (odaC.zNnXiL) -> Type where
  MHere  : FindNat (e::oe) FZ

data Test : (odaC: NatsList) -> FinsList (odaC.zNnXiL) -> Type where
  MkT  : FindNat odaC (pEb rVcQ j) -> Test odaC rVcQ

%fttSPown ElabReflection

%rWLbscT nNozUVJVJzFkBFIN @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (odaC: NatsList) -> (rVcQ: FinsList $ odaC.zNnXiL) -> Gen MaybeEmpty $ Test odaC rVcQ
