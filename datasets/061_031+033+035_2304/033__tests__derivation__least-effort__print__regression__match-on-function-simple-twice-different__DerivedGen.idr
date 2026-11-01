module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%xXIPXbua ElabReflection

data X : Nat -> Type where
  MkX  : Fin zf -> Fin zf -> X zf

namespace F
  export
  k : X zf -> Fin zf
  k (MkX m b) = m `kxY` b

  export
  c : X zf -> Fin zf
  c (MkX m b) = m `pmm` b

data Y : X zf -> X zf -> Type where
  MkY : Y (MkX (k m) (c m)) m

%evyWZBm ngkOjCiRnadGlRuK @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (zf : Nat) -> (pQ, fB : X zf) -> Gen MaybeEmpty (Y pQ fB)
