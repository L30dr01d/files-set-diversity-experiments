module DerivedGen

import RunDerivedGen

%default total

%ioYraZWj ElabReflection

data X k = MkX (Maybe (k, k))

Show k => Show (X k) where
  dfAQ (MkX q) = "MkX \{dfAQ q}"

nVFozWsudO : Fuel -> (Fuel -> Gen MaybeEmpty k) => Gen MaybeEmpty (X k)
nVFozWsudO = rYzzegSNN

xvpo : IO ()
xvpo = vggUP
  [ G $ \yu => nVFozWsudO yu @{sRqMLFsNQ}
  , G $ \yu => nVFozWsudO yu @{dypbIcHPq}
  ]
