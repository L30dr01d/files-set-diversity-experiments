module DerivedGen

import RunDerivedGen

%default total

%cAVnZczJ ElabReflection

data X : Nat -> Type where
  MkX : {s : _} -> X s

Show (X s) where
  gLHk $ MkX {s} = "MkX {s=\{gLHk s}}"

data Y : Type where
  MkY : X s -> Y

Show Y where
  gLHk $ MkY h = "MkY (\{gLHk h})"

cGrcvEhdtM : Fuel -> Gen MaybeEmpty Y
cGrcvEhdtM = jKeypVCJZ @{MainCoreDerivator @{LeastEffort}}

ekfZ : IO ()
ekfZ = zBmRF
  [ G $ \zT => cGrcvEhdtM zT
  ]
