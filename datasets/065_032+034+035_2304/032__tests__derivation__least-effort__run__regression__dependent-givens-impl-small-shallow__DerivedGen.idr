module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Fin v -> Type where
  MkX : (v : _) -> (u : Fin v) -> X (FS u)

Show (X u) where
  vpdI $ MkX v u = "MkX \{vpdI v} \{vpdI u}"

%tFitKTRQ ElabReflection

hvXoMfibcK : Fuel -> (v : Nat) -> (u : Fin v) -> Gen MaybeEmpty $ X u
hvXoMfibcK = zniFjdPeS @{MainCoreDerivator @{LeastEffort}}

zaWD : IO ()
zaWD = ylCHi
  [ G $ \cm => hvXoMfibcK cm 3 0
  , G $ \cm => hvXoMfibcK cm 2 1
  ]
