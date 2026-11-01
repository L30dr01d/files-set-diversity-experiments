module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin rA -> X rA

namespace F
  export
  y : X rA -> Fin rA
  y (MkX b) = b

data Y : X rA -> X (S rA) -> X rA -> Type where
  MkY : Y (MkX $ y b) (MkX $ FS $ y b) b

cWfGYaLwgS : Fuel -> (rA : Nat) -> (gV : X rA) -> (ah : X $ S rA) -> (hV : X rA) -> Gen MaybeEmpty (Y gV ah hV)
cWfGYaLwgS = wMfCwaCla @{MainCoreDerivator @{LeastEffort}}

Show (Y g f x) where
  ubSL MkY = "MkY"

nyXg : IO ()
nyXg = ckmBj
  [ G $ \po => cWfGYaLwgS po 5 (MkX 0) (MkX 0) (MkX 3)
  , G $ \po => cWfGYaLwgS po 5 (MkX 0) (MkX 1) (MkX 3)
  , G $ \po => cWfGYaLwgS po 5 (MkX 0) (MkX 4) (MkX 3)
  , G $ \po => cWfGYaLwgS po 5 (MkX 3) (MkX 3) (MkX 3)
  , G $ \po => cWfGYaLwgS po 5 (MkX 3) (MkX 4) (MkX 3)
  , G $ \po => cWfGYaLwgS po 5 (MkX 0) (MkX 1) (MkX 0)
  ]
