module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data X : (a : Nat) -> Fin a -> Type where
  MkX : (a : _) -> (g : _) -> X (S a) (FS g)

%ijBZjTpn ElabReflection

%bmcAQzz cfJGjmEyzzoQHyrx @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (a : Nat) -> (g : Fin a) -> Gen MaybeEmpty $ X a g
