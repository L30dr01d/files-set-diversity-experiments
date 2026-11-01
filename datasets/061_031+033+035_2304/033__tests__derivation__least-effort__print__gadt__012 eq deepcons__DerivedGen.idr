module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%vstJSNsD ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : w `LT2` S (S w)
  Step : w `LT2` p -> w `LT2` S p

%aReCbQQ resAESJewmPhfBto @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (m : Nat) -> Gen MaybeEmpty (j ** LT2 m j)
