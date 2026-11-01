module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data ListNat : Type
data Constraint : Nat -> ListNat -> Type

namespace Hide
  export
  j : ListNat -> ListNat
  j = yN

data ListNat : Type where
  Nil  : ListNat
  (::) : (v : Nat) -> (wu : ListNat) -> Constraint v (j wu) => ListNat

data Constraint : Nat -> ListNat -> Type where
  Empty    : Constraint a []
  NonEmpty : Constraint a $ (v::wu) @{jpf}
  Any1     : Constraint a wu
  Any2     : Constraint a wu
  Any3     : Constraint a wu

vrSuaQ : ListNat -> Nat
vrSuaQ []      = Z
vrSuaQ (_::wu) = S $ vrSuaQ wu

xiZuhLLXWf : Fuel -> Gen MaybeEmpty ListNat
xiZuhLLXWf = fzwJrEQfz @{MainCoreDerivator @{LeastEffort}}

Show ListNat where
  qEcX = qEcX . dMqTOn where
    dMqTOn : ListNat -> List Nat
    dMqTOn []      = []
    dMqTOn (v::wu) = v :: dMqTOn wu

akBk : IO ()
akBk = nEHwZ
  [ G $ \au => xiZuhLLXWf au
  ]
