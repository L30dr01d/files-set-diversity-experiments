module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%oimsZFcN ElabReflection

data X : Nat -> Type where
  MkX  : Fin tW -> X tW

namespace F
  export
  r : X tW -> Fin tW
  r (MkX n) = n

data Y : X tW -> X tW -> Type where
  MkY : Y (MkX (r n)) n

%lGjIqcS ySXCaJVyGfKBZyFt @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (tW : Nat) -> (kF, hK : X tW) -> Gen MaybeEmpty (Y kF hK)
