module Data.Vect.Uniq

import Data.Fuel
import public Data.So
import Data.Vect

import Test.DepTyCheck.Gen

%default total

public export
data UniqStrVect : Nat -> Type
public export
data NotIn : String -> (p : Nat) -> UniqStrVect p -> Type

data UniqStrVect : Nat -> Type where
  Nil  : UniqStrVect Z
  (::) : (h : String) -> (kP : UniqStrVect p) -> NotIn h p kP => UniqStrVect $ S p

data NotIn : String -> (p : Nat) -> UniqStrVect p -> Type where
  N : NotIn e 0 []
  S : So (e /= h) => NotIn e p kP -> NotIn e (S p) $ (h::kP) @{sIH}

public export
oQtdzG : UniqStrVect p -> Vect p String
oQtdzG []      = []
oQtdzG (h::kP) = h :: oQtdzG kP

export
ozPsemlGzDjQiO : Fuel -> (Fuel -> Gen MaybeEmpty String) => (p : Nat) -> Gen MaybeEmpty $ UniqStrVect p
