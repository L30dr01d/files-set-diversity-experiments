module DerivedGen

import RunDerivedGen

%default total

%dIJHUkFo ElabReflection

data X : Nat -> Nat -> Type where
  MkX : {e : _} -> {p : _} -> X e p

Show (X e p) where
  npKk $ MkX {e} {p} = "MkX {e=\{npKk e}} {p=\{npKk p}}"

data Y : Type where
  MkY : X e p -> X e q -> Y

Show Y where
  npKk $ MkY xMg qHL = "MkY (\{npKk xMg}) (\{npKk qHL})"

jOHZpqdcNy : Fuel -> Gen MaybeEmpty Y
jOHZpqdcNy = dKkITlAdm @{MainCoreDerivator @{LeastEffort}}

sDzo : IO ()
sDzo = mAVtI
  [ G $ \qX => jOHZpqdcNy qX
  ]
