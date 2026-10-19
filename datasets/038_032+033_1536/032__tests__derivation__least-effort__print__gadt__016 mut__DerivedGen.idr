module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data ListNat : Type
data Constraint : Nat -> ListNat -> Type

data ListNat : Type where
  Nil  : ListNat
  (::) : (p : Nat) -> (ry : ListNat) -> Constraint p ry => ListNat

data Constraint : Nat -> ListNat -> Type where
  Empty    : Constraint g []
  NonEmpty : Constraint g $ (p::ry) @{aLW}
  Any1     : Constraint g ry
  Any2     : Constraint g ry
  Any3     : Constraint g ry

%qtjRXbFG ElabReflection

%zzoMrfM restlflSxrDhwImt @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty ListNat
