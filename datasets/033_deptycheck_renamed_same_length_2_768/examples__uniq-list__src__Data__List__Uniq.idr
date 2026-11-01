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
  (::) : (q : String) -> (qS : UniqStrList) -> q `NotIn` qS => UniqStrList

data NotIn : String -> UniqStrList -> Type where
  N : NotIn k []
  S : So (k /= q) => k `NotIn` qS -> k `NotIn` (q::qS) @{tbv}

public export
kGoTXw : UniqStrList -> List String
kGoTXw []      = []
kGoTXw (q::qS) = q :: kGoTXw qS

public export
ivsjke : UniqStrList -> Nat
ivsjke []      = Z
ivsjke (_::oR) = S $ ivsjke oR

export
fNpzLkXbVHoCYR : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty UniqStrList
