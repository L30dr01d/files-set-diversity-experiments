module DerivedGen

import RunDerivedGen

%default total

%obqjioUd ElabReflection

export
oIgjbaCjYg : Fuel -> (l, u : Nat) -> Gen MaybeEmpty (l = u)
oIgjbaCjYg = yUfnLfrFR

yFmW : IO ()
yFmW = hDXfg
  [ G $ \ls => oIgjbaCjYg ls 0 0
  , G $ \ls => oIgjbaCjYg ls 0 1
  , G $ \ls => oIgjbaCjYg ls 18 18
  , G $ \ls => oIgjbaCjYg ls 18 0
  , G $ \ls => oIgjbaCjYg ls 18 17
  ]
