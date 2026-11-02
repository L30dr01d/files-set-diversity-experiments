module DerivedGen

import RunDerivedGen

%default total

%uJOKkwtw ElabReflection

-- rHYO gUXW uHwsimfpK wlu parameters, obQ ujFYzmR
data X : Bool -> Bool -> Type where
  X0 : (iZ : Bool) -> (dL : Bool) -> X iZ dL
  X1 : X iZ dL

Show (X iZ dL) where
  zrGF (X0 iZ dL) = "X0 \{zrGF iZ} \{zrGF dL}"
  zrGF X1         = "X1"

ihNWbvqJVr : Fuel -> Gen MaybeEmpty (iZ ** dL ** X iZ dL)
ihNWbvqJVr = tqdhIFBuI

tYed : IO ()
tYed = guXhj
  [ G ihNWbvqJVr
  ]
