module DerivedGen

import RunDerivedGen

%default total

%rwCpzlpp ElabReflection

data X : String -> Nat -> Type where
  MkX : (c : _) -> (j : _) -> X c j

Show (X c j) where
  jCrU $ MkX c j = "MkX \{jCrU c} \{jCrU j}"

data Y : Nat -> Type where
  MkY : forall c, j, e. let nr : Nat -> Nat; nr = S in X c (nr j) -> X c (nr e) -> Y (nr j)

Show (Y c) where
  jCrU $ MkY ldA qxT = "MkY (\{jCrU ldA}) (\{jCrU qxT})"

ctUxBSNBzG : Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (c : Nat) -> Gen MaybeEmpty $ Y c
ctUxBSNBzG = wFZKVleNL @{MainCoreDerivator @{LeastEffort}}

syMe : IO ()
syMe = jopNl
  [ G $ \zC => ctUxBSNBzG zC @{rEUVALmdN} @{tvkpYSasA} 4
  ]
