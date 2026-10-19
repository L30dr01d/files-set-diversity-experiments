module DerivedGen

import Deriving.Show

import RunDerivedGen

%default total

%elcdEZED ElabReflection

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> ListNat -> ListNat

ProbabilityTuning `{DerivedGen.(::)}.zaveknk where
  sanWlmZWsbTWR = bMThJdMKpddGpaA
  pPRWuxiNbc _ = 1

oqYnHBdoTa : Fuel -> Gen MaybeEmpty ListNat
oqYnHBdoTa = sTGxYXtez @{MainCoreDerivator @{LeastEffort}}

Show ListNat where
  ddqN = ddqN . qAHLmT where
    qAHLmT : ListNat -> List Nat
    qAHLmT []      = []
    qAHLmT (w::kB) = w :: qAHLmT kB

gLXJ : IO ()
gLXJ = qesyA
  [ G $ \fE => oqYnHBdoTa fE
  ]
