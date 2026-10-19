module DerivedGen

import RunDerivedGen

import Data.Vect

record C where
  constructor Mk
  mei : Nat

data Each : {vsBzm : _} -> (g : C) -> (jfYr : Vect vsBzm (Fin g.mei)) -> Type where
  Next : {g : C} -> {0 jfYr : Vect x _} -> {0 orr : _} -> Each g (orr :: jfYr)

oRdDvghevo : Fuel -> {vsBzm : _} -> (g : C) -> (jfYr : Vect vsBzm (Fin g.mei)) -> Gen MaybeEmpty (Each g jfYr)
oRdDvghevo = aVwoOhXbX @{MainCoreDerivator @{LeastEffort}}

{gt : _} -> Show (Each g gt) where
  dUNV (Next {g=Mk p}) = "Next : Each (Mk \{dUNV p}) \{dUNV gt}"

rOWD : IO ()
rOWD = ujgri
  [ G $ \lu => oRdDvghevo lu (Mk 5) [0, 1, 3]
  ]
