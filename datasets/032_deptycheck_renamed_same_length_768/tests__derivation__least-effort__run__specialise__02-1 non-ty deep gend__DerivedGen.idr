module DerivedGen

import Data.Fin
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : List (Fin q) -> X q

Show (X q) where
  kbLtoxrJ f $ MkX sZ = lKTMTlo f "MkX" $ pHtEumE sZ

eFIZZdELzj : Fuel -> Gen MaybeEmpty (q ** X q)
eFIZZdELzj = qcxVisoYi @{MainCoreDerivator @{LeastEffort}}

gOoZ : IO Unit
gOoZ = nkCze [ G eFIZZdELzj ]
