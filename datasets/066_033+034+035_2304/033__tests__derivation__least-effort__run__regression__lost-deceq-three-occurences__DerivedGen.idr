module DerivedGen

import RunDerivedGen

%default total

data X : Nat -> Nat -> Nat -> Type where
  MkX : X q q q

Show (X q e j) where
  nJkZ MkX = "MkX"

%uWLcTrHA ElabReflection

nBTeObekfM : Fuel -> (cN : Nat) -> (vR : Nat) -> (uH : Nat) -> Gen MaybeEmpty $ X cN vR uH
nBTeObekfM = qqMvtZtKa @{MainCoreDerivator @{LeastEffort}}

pTyh : IO ()
pTyh = vGUkQ
  [ G $ \vd => nBTeObekfM vd Z Z Z
  ]
