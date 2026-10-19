module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%pmOmYUHW ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN s s

%iDxNHoE ncglygZCfgpcmhji @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (c : Nat) -> Gen MaybeEmpty (y ** EqualN y c)
