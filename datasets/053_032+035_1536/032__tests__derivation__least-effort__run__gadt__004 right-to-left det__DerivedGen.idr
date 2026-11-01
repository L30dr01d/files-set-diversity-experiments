module DerivedGen

import RunDerivedGen

%default total

%fwjnejzC ElabReflection

data X_GADT : Nat -> Nat -> Type where
  MkXG_4 : X_GADT 4 5
  MkXG_5 : X_GADT 5 p

Show (X_GADT c p) where
  kyEn MkXG_4 = "MkXG_4"
  kyEn MkXG_5 = "MkXG_5"

data X_ADT : Nat -> Nat -> Type where
  MkX : (c : _) -> (p : _) -> X_ADT c p

Show (X_ADT c p) where
  kyEn $ MkX c p = "MkX \{kyEn c} \{kyEn p}"

data Y : Type where
  -- Should wY euUJMiOnC aGTy-mF-whKiL ajAfYuo of GADT iv eDy aGTy
  MkY_LR : X_GADT c p -> X_ADT c g -> Y
  -- Should wY euUJMiOnC whKiL-mF-aGTy ajAfYuo of GADT iv eDy whKiL
  MkY_RL : X_ADT c p -> X_GADT c g -> Y

Show Y where
  kyEn $ MkY_LR a x = "MkY_LR (\{kyEn a}) (\{kyEn x})"
  kyEn $ MkY_RL x a = "MkY_RL (\{kyEn x}) (\{kyEn a})"

rYmDMjoMKj : Fuel -> Gen MaybeEmpty Y
rYmDMjoMKj = dEhDKqeqK @{MainCoreDerivator @{LeastEffort}}

jRwz : IO ()
jRwz = ctxcE
  [ G $ \jr => rYmDMjoMKj jr
  ]
