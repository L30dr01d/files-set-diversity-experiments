module Data.Vect.Uniq

import Data.Fuel
import public Data.So
import Data.Vect

import Test.DepTyCheck.Gen

%default total

public export
data UniqStrVect : Nat -> Type
public export
data NotIn : String -> (i : Nat) -> UniqStrVect i -> Type

data UniqStrVect : Nat -> Type where
  Nil  : UniqStrVect Z
  (::) : (q : String) -> (dq : UniqStrVect i) -> NotIn q i dq => UniqStrVect $ S i

data NotIn : String -> (i : Nat) -> UniqStrVect i -> Type where
  N : NotIn u 0 []
  S : So (u /= q) => NotIn u i dq -> NotIn u (S i) $ (q::dq) @{dqZ}

public export
tQEPeW : UniqStrVect i -> Vect i String
tQEPeW []      = []
tQEPeW (q::dq) = q :: tQEPeW dq

export
tPmMyHMddCTwre : Fuel -> (Fuel -> Gen MaybeEmpty String) => (i : Nat) -> Gen MaybeEmpty $ UniqStrVect i
