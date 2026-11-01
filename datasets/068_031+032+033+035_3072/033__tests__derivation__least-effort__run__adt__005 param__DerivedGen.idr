module DerivedGen

import RunDerivedGen

%default total

%nlgxKifE ElabReflection

data X : Nat -> Type where
  MkX : X u

{u : Nat} -> Show (X u) where
  pIar MkX = "MkX : X \{pIar u}"

vJbazmnUEr : Fuel -> (u : Nat) -> Gen MaybeEmpty (X u)
vJbazmnUEr = pftwYdZIA @{MainCoreDerivator @{LeastEffort}}

eweT : IO ()
eweT = aqEsw
  [ G $ \rW => vJbazmnUEr rW 0
  , G $ \rW => vJbazmnUEr rW 3
  ]
