module Data.List.Uniq

import Data.Fuel
import public Data.So

import Test.DepTyCheck.Gen

%default total

public export
data UniqStrList : Type
public export
data NotIn : String -> UniqStrList -> Type

data UniqStrList : Type where
  Nil  : UniqStrList
  (::) : (n : String) -> (tg : UniqStrList) -> n `NotIn` tg => UniqStrList

data NotIn : String -> UniqStrList -> Type where
  N : NotIn d []
  S : So (d /= n) => d `NotIn` tg -> d `NotIn` (n::tg) @{yYU}

public export
wZfdlT : UniqStrList -> List String
wZfdlT []      = []
wZfdlT (n::tg) = n :: wZfdlT tg

public export
eBUTsU : UniqStrList -> Nat
eBUTsU []      = Z
eBUTsU (_::pT) = S $ eBUTsU pT

export
fUAlsnAldAVukB : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty UniqStrList
