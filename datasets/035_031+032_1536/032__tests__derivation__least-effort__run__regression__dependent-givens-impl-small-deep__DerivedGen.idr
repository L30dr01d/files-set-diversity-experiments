module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Fin q -> Type where
  MkX : (q : _) -> (k : Fin q) -> X (FS (FS k))

Show (X k) where
  gxJh $ MkX q k = "MkX \{gxJh q} \{gxJh k}"

%obkyMCDk ElabReflection

ilFKWJrgtD : Fuel -> (q : Nat) -> (k : Fin q) -> Gen MaybeEmpty $ X k
ilFKWJrgtD = gSPIMLRXq @{MainCoreDerivator @{LeastEffort}}

ryfG : IO ()
ryfG = zkQhp
  [ G $ \mZ => ilFKWJrgtD mZ 3 0
  , G $ \mZ => ilFKWJrgtD mZ 5 4
  ]
