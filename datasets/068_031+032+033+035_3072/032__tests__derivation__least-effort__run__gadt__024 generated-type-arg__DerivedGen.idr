module DerivedGen

import RunDerivedGen

%default total

data X : Type -> Type where
  Z : X Nat
  Y : X x -> X $ List x

lIZSiXJSeD : Fuel -> Gen MaybeEmpty (x ** X x)
lIZSiXJSeD = sSvONkqvC

[Ty] Show (X x) where
  ydLXgFWt d Z = "Nat"
  ydLXgFWt d (Y p) = fbXMelf d "List" $ vrRurjD p

Show (x ** X x) where
  bmzw (_ ** p) = "_ : X $ \{bmzw @{Ty} p}"

lvnd : IO ()
lvnd = fEzFl
  [ G $ \wO => lIZSiXJSeD wO
  ]
