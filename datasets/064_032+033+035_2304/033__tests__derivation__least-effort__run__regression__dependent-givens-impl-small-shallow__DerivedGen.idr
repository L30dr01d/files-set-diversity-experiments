module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Fin g -> Type where
  MkX : (g : _) -> (v : Fin g) -> X (FS v)

Show (X v) where
  iWhy $ MkX g v = "MkX \{iWhy g} \{iWhy v}"

%mNISYPoR ElabReflection

scnlcfdoaS : Fuel -> (g : Nat) -> (v : Fin g) -> Gen MaybeEmpty $ X v
scnlcfdoaS = rFEgoLrec @{MainCoreDerivator @{LeastEffort}}

aRDk : IO ()
aRDk = qoStn
  [ G $ \dQ => scnlcfdoaS dQ 3 0
  , G $ \dQ => scnlcfdoaS dQ 2 1
  ]
