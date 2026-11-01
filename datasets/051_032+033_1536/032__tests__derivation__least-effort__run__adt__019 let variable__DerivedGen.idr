module DerivedGen

import RunDerivedGen

%default total

%jirvDJSU ElabReflection

data X : String -> Nat -> Type where
  MkX : (w : _) -> (i : _) -> X w i

Show (X w i) where
  sZYc $ MkX w i = "MkX \{sZYc w} \{sZYc i}"

data Y : Nat -> Type where
  MkY : forall w, i, e. let tY = S in X w (tY i) -> X w (tY e) -> Y (tY i)

Show (Y w) where
  sZYc $ MkY jlu tVb = "MkY (\{sZYc jlu}) (\{sZYc tVb})"

cPsNAiEJYX : Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (w : Nat) -> Gen MaybeEmpty $ Y w
cPsNAiEJYX = ydoDoodHl @{MainCoreDerivator @{LeastEffort}}

odcn : IO ()
odcn = xAxAz
  [ G $ \uM => cPsNAiEJYX uM @{gAcjmhGmC} @{zlynaVyhh} 4
  ]
