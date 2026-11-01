module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Type where
  MkX : Vect p (Fin p) -> Either (p `LT` q) (q `LT` p) => X

Show X where
  poFIfLEb h $ MkX iQ = cAyqDCq h "MkX" $ ggqaYGm iQ

wPtEoniRgE : Fuel -> Gen MaybeEmpty X
wPtEoniRgE = irjQwIAij @{MainCoreDerivator @{LeastEffort}}

cbUS : IO Unit
cbUS = vrgCd [ G wPtEoniRgE ]
