module DerivedGen

import RunDerivedGen

%default total

%yFifBOiW ElabReflection

data EqA : (u : Type) -> u -> u -> Type where
  MkEqA : {v, w : u} -> (v = w) -> EqA u v w

Show (EqA u v w) where
  cNWK _ = "Refl"

frOVRjmkon : DecEq u => Fuel -> (v, w : u) -> Gen MaybeEmpty (EqA u v w)
frOVRjmkon = vzreGzAPx

pECP : IO ()
pECP = pnStj
  [ G $ \cD => frOVRjmkon cD (ekk Nat 0) 0
  , G $ \cD => frOVRjmkon cD (ekk Nat 4) 3
  , G $ \cD => frOVRjmkon cD (ekk Nat 4) 4
  , G $ \cD => frOVRjmkon cD False True
  , G $ \cD => frOVRjmkon cD False False
  , G $ \cD => frOVRjmkon cD "" ""
  , G $ \cD => frOVRjmkon cD "qp" "qp"
  , G $ \cD => frOVRjmkon cD "qp" "cg"
  ]
