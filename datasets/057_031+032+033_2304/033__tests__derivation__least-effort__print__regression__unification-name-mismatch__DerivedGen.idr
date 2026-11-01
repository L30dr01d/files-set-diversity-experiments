module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%hNMylvXi ElabReflection

data X : Type where
  Nil : X
  (::) : Unit -> X -> X

data Y : (ro : X) -> (mB : X) -> Type where
  A : Y (h :: ro) (h :: ro)
  B : Y ro mB -> Y (h :: ro) (s :: mB)

%oVnMEHR wluZQDJGzKLdTdAT $ Fuel -> (ro : X) -> (mB : X) -> Gen MaybeEmpty $ Y ro mB
