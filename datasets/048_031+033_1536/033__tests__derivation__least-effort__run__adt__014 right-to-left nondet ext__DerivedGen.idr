module DerivedGen

import RunDerivedGen

%default total

%xlOXrWfm ElabReflection

data X : String -> Nat -> Type where
  MkX : (a : _) -> (c : _) -> X a c

Show (X a c) where
  xGTl $ MkX a c = "MkX \{xGTl a} \{xGTl c}"

data Y : Type where
  MkY : X a c -> X a x -> Y

Show Y where
  xGTl $ MkY pqW wxH = "MkY (\{xGTl pqW}) (\{xGTl wxH})"

apEMbHDJAo : Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty Y
apEMbHDJAo = cxHquScTp @{MainCoreDerivator @{LeastEffort}}

hWun : IO ()
hWun = mZWPf
  [ G $ \uw => apEMbHDJAo uw @{nSIDXQQIP} @{rMmmyIgHE}
  ]
