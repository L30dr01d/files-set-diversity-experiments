module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%wkvGtPuk ElabReflection

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> ListNat -> ListNat

ProbabilityTuning `{DerivedGen.(::)}.eIndcnQ where
  mPoPnsZmdSMEP = hiRYJgJLRYpWXuU
  qBBBFufLjY _ = 1

%dfmNlEA jdIZYYeTKRfzmsfW @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty ListNat
