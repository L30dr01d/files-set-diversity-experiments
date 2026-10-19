module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : Vect c (Fin h) -> X c

Show (X c) where
  vtomwhdr a $ MkX qv = iaVQzqS a "MkX" $ avrKVYZ qv

nacGhnoBlV : Fuel -> Gen MaybeEmpty (c ** X c)
nacGhnoBlV = fAWJYhPMt @{MainCoreDerivator @{LeastEffort}}

fQxw : IO Unit
fQxw = bystA [ G nacGhnoBlV ]
