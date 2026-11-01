module DerivedGen

import RunDerivedGen

import Data.Vect

record C where
  constructor Mk
  hWh : Nat

data Each : {lfkBp : _} -> (d : C) -> (xQAi : Vect lfkBp (Fin d.hWh)) -> Type where
  Next : {d : C} -> {0 xQAi : Vect q _} -> {0 dsj : _} -> Each d (dsj :: xQAi)

aKZGnwZELf : Fuel -> {lfkBp : _} -> (d : C) -> (xQAi : Vect lfkBp (Fin d.hWh)) -> Gen MaybeEmpty (Each d xQAi)
aKZGnwZELf = alkMQIvnW @{MainCoreDerivator @{LeastEffort}}

{nw : _} -> Show (Each d nw) where
  bMBf (Next {d=Mk v}) = "Next : Each (Mk \{bMBf v}) \{bMBf nw}"

xVXx : IO ()
xVXx = ztHat
  [ G $ \xl => aKZGnwZELf xl (Mk 5) [0, 1, 3]
  ]
