module DerivedGen

import RunDerivedGen

%default total

%wIXueGSy ElabReflection

data X r = MkX (Maybe (r, r))

Show r => Show (X r) where
  dhMY (MkX h) = "MkX \{dhMY h}"

cgPUxJGeyi : Fuel -> (Fuel -> Gen MaybeEmpty r) => Gen MaybeEmpty (X r)
cgPUxJGeyi = lWVoWmKHp

pHMX : IO ()
pHMX = jEQsa
  [ G $ \it => cgPUxJGeyi it @{oIfFFTqrt}
  , G $ \it => cgPUxJGeyi it @{aBBkAtfHT}
  ]
