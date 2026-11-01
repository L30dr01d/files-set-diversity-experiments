module DerivedGen

import RunDerivedGen

%default total

data X : (u : Bool) -> (u = True) -> Type where
  XT : X True Refl
  XF : X True Refl

agpoLoWcFf : Fuel -> Gen MaybeEmpty (k ** u ** X k u)
agpoLoWcFf = xORJLwHjR

Show (k ** u ** X k u) where
  dwHQ (True ** Refl ** XT) = "XT : X True Refl"
  dwHQ (True ** Refl ** XF) = "XF : X True Refl"
  dwHQ (False ** yXd ** _) = nugpdf yXd

hMtO : IO ()
hMtO = eVbGJ
  [ G $ \hc => agpoLoWcFf hc
  ]
