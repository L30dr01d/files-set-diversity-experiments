module DerivedGen

import RunDerivedGen

%default total

%injSKnyG ElabReflection

data X : Nat -> Type where
  MkX : X p

{p : Nat} -> Show (X p) where
  cDqW MkX = "MkX : X \{cDqW p}"

vPHIoSwZgj : Fuel -> Gen MaybeEmpty (p ** X p)
vPHIoSwZgj = wtmajefzT @{MainCoreDerivator @{LeastEffort}}

gfEY : IO ()
gfEY = jPDIC
  [ G $ \vd => vPHIoSwZgj vd
  ]
