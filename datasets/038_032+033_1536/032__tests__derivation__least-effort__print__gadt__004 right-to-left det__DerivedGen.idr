module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%mrXvLdlE ElabReflection

data X_GADT : Nat -> Nat -> Type where
  MkXG_4 : X_GADT 4 5
  MkXG_5 : X_GADT 5 g

data X_ADT : Nat -> Nat -> Type where
  MkX : (o : _) -> (g : _) -> X_ADT o g

data Y : Type where
  -- Should kW uMuCxIrWB hOYh-uf-lBclH fIsxzLx of GADT sb fbq hOYh
  MkY_LR : X_GADT o g -> X_ADT o f -> Y
  -- Should kW uMuCxIrWB lBclH-uf-hOYh fIsxzLx of GADT sb fbq lBclH
  MkY_RL : X_ADT o g -> X_GADT o f -> Y

%wottQQY aupWtKIjJWQYwcJW @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y
