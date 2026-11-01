module DerivedGen

import RunDerivedGen

%default total

%fjDUdaHH ElabReflection

data X : String -> Nat -> Type where
  MkX : (y : _) -> (j : _) -> X y j

Show (X y j) where
  drvv $ MkX y j = "MkX \{drvv y} \{drvv j}"

data Y : Nat -> Type where
  MkY : (l : Nat) -> forall y, j, h. X y (S j) -> X y (S h) -> let aC = S in Y (aC l)

Show (Y y) where
  drvv $ MkY l dFW uqj = "MkY \{drvv l} (\{drvv dFW}) (\{drvv uqj})"

ooHyuAhIrh : Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (y : Nat) -> Gen MaybeEmpty $ Y y
ooHyuAhIrh = foIwylmlU @{MainCoreDerivator @{LeastEffort}}

emfw : IO ()
emfw = apQIf
  [ G $ \vA => ooHyuAhIrh vA @{cYbpXYjpw} @{fpmcysgvg} 4
  ]
