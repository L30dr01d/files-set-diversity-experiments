module DerivedGen

import Deriving.Show

import RunDerivedGen

%default total

%gGYVtCjh ElabReflection

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> ListNat -> ListNat

ProbabilityTuning `{DerivedGen.(::)}.jcUTNvC where
  haZRihCcGxBwy = eXOMcFJeFhNzFWA
  ksjmnHjKJU _ = 1

sTOprWqdZi : Fuel -> Gen MaybeEmpty ListNat
sTOprWqdZi = mITttRlxA @{MainCoreDerivator @{LeastEffort}}

Show ListNat where
  mQoK = mQoK . wkAjlH where
    wkAjlH : ListNat -> List Nat
    wkAjlH []      = []
    wkAjlH (d::hw) = d :: wkAjlH hw

cmco : IO ()
cmco = brnlz
  [ G $ \ks => sTOprWqdZi ks
  ]
