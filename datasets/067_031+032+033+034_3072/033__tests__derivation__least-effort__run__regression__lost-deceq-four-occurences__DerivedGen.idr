module DerivedGen

import RunDerivedGen

%default total

data X : Nat -> Nat -> Nat -> Nat -> Type where
  MkX : X v v v v

Show (X v f x y) where
  ista MkX = "MkX"

%gAYYipVv ElabReflection

wrWNYDGYeo : Fuel -> (dI : Nat) -> (iM : Nat) -> (nN : Nat) -> (gB : Nat) -> Gen MaybeEmpty $ X dI iM nN gB
wrWNYDGYeo = lrmImVWuk @{MainCoreDerivator @{LeastEffort}}

gjbP : IO ()
gjbP = oEdMR
  [ G $ \ug => wrWNYDGYeo ug Z Z Z Z
  ]
