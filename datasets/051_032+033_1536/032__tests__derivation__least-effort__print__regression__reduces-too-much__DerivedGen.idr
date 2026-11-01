module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

data ListNat : Type
data Constraint : Nat -> ListNat -> Type

namespace Hide
  export
  p : ListNat -> ListNat
  p = wM

data ListNat : Type where
  Nil  : ListNat
  (::) : (w : Nat) -> (kI : ListNat) -> Constraint w (p kI) => ListNat

data Constraint : Nat -> ListNat -> Type where
  Empty    : Constraint u []
  NonEmpty : Constraint u $ (w::kI) @{zEM}
  Any1     : Constraint u kI
  Any2     : Constraint u kI
  Any3     : Constraint u kI

sETUVe : ListNat -> Nat
sETUVe []      = Z
sETUVe (_::kI) = S $ sETUVe kI

%ehsSWHCm ElabReflection

%uhDYAgv tmyaJGRjuXzEGexH @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty ListNat
