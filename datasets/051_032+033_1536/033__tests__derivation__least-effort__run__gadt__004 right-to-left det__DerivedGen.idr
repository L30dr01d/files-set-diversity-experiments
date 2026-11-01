module DerivedGen

import RunDerivedGen

%default total

%lUSKSxjh ElabReflection

data X_GADT : Nat -> Nat -> Type where
  MkXG_4 : X_GADT 4 5
  MkXG_5 : X_GADT 5 j

Show (X_GADT g j) where
  uwzM MkXG_4 = "MkXG_4"
  uwzM MkXG_5 = "MkXG_5"

data X_ADT : Nat -> Nat -> Type where
  MkX : (g : _) -> (j : _) -> X_ADT g j

Show (X_ADT g j) where
  uwzM $ MkX g j = "MkX \{uwzM g} \{uwzM j}"

data Y : Type where
  -- Should bJ wWLYSZsST jUHa-ig-tdUpq tvmzksG of GADT cs yeP jUHa
  MkY_LR : X_GADT g j -> X_ADT g i -> Y
  -- Should bJ wWLYSZsST tdUpq-ig-jUHa tvmzksG of GADT cs yeP tdUpq
  MkY_RL : X_ADT g j -> X_GADT g i -> Y

Show Y where
  uwzM $ MkY_LR k f = "MkY_LR (\{uwzM k}) (\{uwzM f})"
  uwzM $ MkY_RL f k = "MkY_RL (\{uwzM f}) (\{uwzM k})"

vaZrTxpShc : Fuel -> Gen MaybeEmpty Y
vaZrTxpShc = nWHyLackD @{MainCoreDerivator @{LeastEffort}}

mJBi : IO ()
mJBi = wqwRS
  [ G $ \em => vaZrTxpShc em
  ]
