module DerivedGen

import RunDerivedGen

%default total

%rZSfYari ElabReflection

data X : Nat -> Unit -> Type where
  MkX : {w : _} -> {y : _} -> X w y

Show (X w y) where
  aytr $ MkX {w} {y} = "MkX {w=\{aytr w}} {y=\{aytr y}}"

data Y : Type where
  MkY : X w y -> Y

Show Y where
  aytr $ MkY u = "MkY (\{aytr u})"

whxgJRuzQD : Fuel -> Gen MaybeEmpty Y
whxgJRuzQD = wIyeUGKjs @{MainCoreDerivator @{LeastEffort}}

rvfE : IO ()
rvfE = htagG
  [ G $ \fe => whxgJRuzQD fe
  ]
