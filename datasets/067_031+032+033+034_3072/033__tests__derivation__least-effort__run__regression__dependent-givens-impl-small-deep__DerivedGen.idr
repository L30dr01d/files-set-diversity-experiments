module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Fin a -> Type where
  MkX : (a : _) -> (p : Fin a) -> X (FS (FS p))

Show (X p) where
  tfvk $ MkX a p = "MkX \{tfvk a} \{tfvk p}"

%pGPznrio ElabReflection

unyjeulmXk : Fuel -> (a : Nat) -> (p : Fin a) -> Gen MaybeEmpty $ X p
unyjeulmXk = gnVnYcETG @{MainCoreDerivator @{LeastEffort}}

rwKk : IO ()
rwKk = pglbj
  [ G $ \gU => unyjeulmXk gU 3 0
  , G $ \gU => unyjeulmXk gU 5 4
  ]
