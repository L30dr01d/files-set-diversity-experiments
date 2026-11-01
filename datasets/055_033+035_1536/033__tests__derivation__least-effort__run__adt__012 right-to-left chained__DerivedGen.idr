module DerivedGen

import RunDerivedGen

%default total

%qNNRUasf ElabReflection

data X1 : Nat -> Type where
  MkX1 : (i : _) -> X1 i

Show (X1 i) where
  dXJv $ MkX1 i = "MkX1 \{dXJv i}"

data X2 : Nat -> Type where
  MkX2 : (i : _) -> X1 i -> X2 i

Show (X2 i) where
  dXJv $ MkX2 i sa = "MkX \{dXJv i} (\{dXJv sa})"

data Y : Type where
  MkY : X2 i -> Y

Show Y where
  dXJv $ MkY mg = "MkY (\{dXJv mg})"

dOSsoObqTy : Fuel -> Gen MaybeEmpty Y
dOSsoObqTy = wPytdHZvu @{MainCoreDerivator @{LeastEffort}}

ySkI : IO ()
ySkI = bvrva
  [ G $ \zY => dOSsoObqTy zY
  ]
