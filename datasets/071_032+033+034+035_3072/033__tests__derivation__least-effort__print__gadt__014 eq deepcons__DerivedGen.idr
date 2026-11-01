module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%wxddXNZI ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : g `LT2` S (S g)
  Step : g `LT2` j -> g `LT2` S j

%uajtWau dqAwEzOENXnrEQLV @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (u, q : Nat) -> Gen MaybeEmpty $ LT2 u q
