module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%xHUUcZIl ElabReflection

data X : Nat -> Type where
  MkX  : Fin uv -> X uv

namespace F
  export
  l : X uv -> Fin uv
  l (MkX n) = n

data Y : X uv -> X (S uv) -> X uv -> Type where
  MkY : Y (MkX $ l n) (MkX $ FS $ l n) n

%qyhelOp aBWhdELGVNiQdSSq @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (uv : Nat) -> (sP : X uv) -> (uV : X $ S uv) -> (yt : X uv) -> Gen MaybeEmpty (Y sP uV yt)
