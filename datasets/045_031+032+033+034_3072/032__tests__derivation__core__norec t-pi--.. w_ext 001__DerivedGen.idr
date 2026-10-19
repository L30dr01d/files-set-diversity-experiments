module DerivedGen

import RunDerivedGen

%default total

%tBJGskiV ElabReflection

data EqA : (k : Type) -> k -> k -> Type where
  MkEqA : {i, x : o} -> (i = x) -> EqA o i x

Show (EqA k i x) where
  cZWJ _ = "Refl"

kCqaKJRiaQ : DecEq k => Fuel -> (i, x : k) -> Gen MaybeEmpty (EqA k i x)
kCqaKJRiaQ = kPoYNwOIC

fUbS : IO ()
fUbS = mglJy
  [ G $ \yR => kCqaKJRiaQ yR (oDt Nat 0) 0
  , G $ \yR => kCqaKJRiaQ yR (oDt Nat 4) 3
  , G $ \yR => kCqaKJRiaQ yR (oDt Nat 4) 4
  , G $ \yR => kCqaKJRiaQ yR False True
  , G $ \yR => kCqaKJRiaQ yR False False
  , G $ \yR => kCqaKJRiaQ yR "" ""
  , G $ \yR => kCqaKJRiaQ yR "us" "us"
  , G $ \yR => kCqaKJRiaQ yR "us" "sg"
  ]
