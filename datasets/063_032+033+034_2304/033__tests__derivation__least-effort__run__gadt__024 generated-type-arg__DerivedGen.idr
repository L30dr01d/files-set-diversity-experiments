module DerivedGen

import RunDerivedGen

%default total

data X : Type -> Type where
  Z : X Nat
  Y : X o -> X $ List o

pVLpgMHamu : Fuel -> Gen MaybeEmpty (o ** X o)
pVLpgMHamu = ibGyIQQkX

[Ty] Show (X o) where
  juZnBDRW r Z = "Nat"
  juZnBDRW r (Y m) = lCnlonf r "List" $ pDxdXeT m

Show (o ** X o) where
  chvg (_ ** m) = "_ : X $ \{chvg @{Ty} m}"

tpit : IO ()
tpit = anRBE
  [ G $ \qO => pVLpgMHamu qO
  ]
