module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%lWkizCCA ElabReflection

data X : Nat -> Type where
  MkX  : Fin ug -> Fin (S ug) -> X ug

namespace F
  export
  u : X ug -> Fin ug
  u (MkX o FZ) = o
  u (MkX o $ FS y) = o `cSa` y

data Y : X ug -> X ug -> Type where
  MkY : Y (MkX (u o) (FS $ u o)) o

%oSmIOqJ rAZSkKsZOdyFZHmt @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (ug : Nat) -> (xq, lo : X ug) -> Gen MaybeEmpty (Y xq lo)
