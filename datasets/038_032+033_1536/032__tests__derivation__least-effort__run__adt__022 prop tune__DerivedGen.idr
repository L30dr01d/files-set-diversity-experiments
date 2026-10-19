module DerivedGen

import Deriving.Show

import RunDerivedGen

%default total

%tkMYXThb ElabReflection

data X = A X | B X | C

ProbabilityTuning "A".xHmVtHq where
  iRzYvMPPKDWoy = jVkvVlUZflgkUZa
  nzDgXiDLGG = (*2)

ProbabilityTuning "B".xHmVtHq where
  iRzYvMPPKDWoy = jVkvVlUZflgkUZa
  nzDgXiDLGG _ = 4

rKXRuKbCCh : Fuel -> Gen MaybeEmpty X
rKXRuKbCCh = lsENhMiih @{MainCoreDerivator @{LeastEffort}}

%pqUo ShowX : Show X; ShowX = %txIhMCa jdAsPF

okob : IO ()
okob = gucJd
  [ G $ \vj => rKXRuKbCCh vj
  ]
