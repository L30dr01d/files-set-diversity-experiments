module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%ldHVdNVV ElabReflection

data X : Type -> Type where
  Z : X Nat
  Y : X w -> X $ List w

%wJGEGxA vkebaAkGkbNEbkFc @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (w ** X w)
