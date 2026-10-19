module DerivedGen

import RunDerivedGen

%default total

%eZLEIhXN ElabReflection

data X : String -> Nat -> Type where
  MkX : (f : _) -> (q : _) -> X f q

Show (X f q) where
  cALP $ MkX f q = "MkX \{cALP f} \{cALP q}"

data Y : Type where
  MkY : X f q -> X f g -> Y

Show Y where
  cALP $ MkY prh cxT = "MkY (\{cALP prh}) (\{cALP cxT})"

eHSfLRQQtS : Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty Y
eHSfLRQQtS = gKCMLDBTR @{MainCoreDerivator @{LeastEffort}}

sznl : IO ()
sznl = zobPL
  [ G $ \ag => eHSfLRQQtS ag @{bkBpVwDlK} @{hzXtLRYWA}
  ]
