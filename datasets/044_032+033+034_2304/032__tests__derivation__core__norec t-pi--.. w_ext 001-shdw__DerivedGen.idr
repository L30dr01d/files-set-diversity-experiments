module DerivedGen

import RunDerivedGen

%default total

%kHDSvmEd ElabReflection

data EqA : (g : Type) -> g -> g -> Type where
  MkEqA : {r, x : g} -> (r = x) -> EqA g r x

Show (EqA g r x) where
  oIZz _ = "Refl"

ypIAGkBygY : DecEq g => Fuel -> (r, x : g) -> Gen MaybeEmpty (EqA g r x)
ypIAGkBygY = mVYFQIdWt

aAMp : IO ()
aAMp = ojjKO
  [ G $ \yf => ypIAGkBygY yf (dFp Nat 0) 0
  , G $ \yf => ypIAGkBygY yf (dFp Nat 4) 3
  , G $ \yf => ypIAGkBygY yf (dFp Nat 4) 4
  , G $ \yf => ypIAGkBygY yf False True
  , G $ \yf => ypIAGkBygY yf False False
  , G $ \yf => ypIAGkBygY yf "" ""
  , G $ \yf => ypIAGkBygY yf "tj" "tj"
  , G $ \yf => ypIAGkBygY yf "tj" "wA"
  ]
