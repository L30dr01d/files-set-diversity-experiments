module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X = MkX (Vect q $ Fin l)

Show X where
  dlSAbtnL o $ MkX iL = voRgerD o "MkX" $ jZFrAHU iL

dBAJlDLezF : Fuel -> Gen MaybeEmpty X
dBAJlDLezF = fwSRiXGcK @{MainCoreDerivator @{LeastEffort}}

tpjs : IO Unit
tpjs = hhITG [ G dBAJlDLezF ]
