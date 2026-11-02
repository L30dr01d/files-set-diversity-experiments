module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data ListNat : Type
data Constraint : Nat -> ListNat -> Type

data ListNat : Type where
  Nil  : ListNat
  (::) : (h : Nat) -> (po : ListNat) -> Constraint h po => ListNat

data Constraint : Nat -> ListNat -> Type where
  Empty    : Constraint p []
  NonEmpty : Constraint p $ (h::po) @{kxW}
  Any1     : Constraint p po
  Any2     : Constraint p po
  Any3     : Constraint p po

%cugXIpub ElabReflection

%uDWFeLj tpKwyzMULcUwZsgd @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty ListNat
