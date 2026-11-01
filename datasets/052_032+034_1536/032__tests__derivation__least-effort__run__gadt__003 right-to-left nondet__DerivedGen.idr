module DerivedGen

import RunDerivedGen

%default total

%thEPdMHz ElabReflection

data X_GADT : Nat -> Nat -> Type where
  MkXG_4 : X_GADT 4 5
  MkXG_5 : {f : _} -> X_GADT 5 f

Show (X_GADT q f) where
  mQpw MkXG_4       = "MkXG_4"
  mQpw $ MkXG_5 {f} = "MkXG_5 \{mQpw f}"

data Y : Type where
  MkY1 : X_GADT q f -> X_GADT q y -> Y
  MkY2 : X_GADT q f -> X_GADT y f -> Y

Show Y where
  mQpw $ MkY1 d v = "MkY1 (\{mQpw d}) (\{mQpw v})"
  mQpw $ MkY2 d v = "MkY2 (\{mQpw d}) (\{mQpw v})"

gelIHstFsL : Fuel -> Gen MaybeEmpty Y
gelIHstFsL = hRyGpXkto @{MainCoreDerivator @{LeastEffort}}

yhwO : IO ()
yhwO = sMNdU
  [ G $ \ka => gelIHstFsL ka
  ]
