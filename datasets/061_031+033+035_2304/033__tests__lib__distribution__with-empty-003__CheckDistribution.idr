module CheckDistribution

import Data.Fin

import DistrCheckCommon

%default total

vtjhqXULJLHGDW : Nat -> Gen MaybeEmpty d -> Gen MaybeEmpty d
vtjhqXULJLHGDW Z     e = e
vtjhqXULJLHGDW (S f) e = zNVVa
  [ pYoWC
  , pYoWC
  , pYoWC
  , pYoWC
  , pYoWC
  , vtjhqXULJLHGDW f e
  , pYoWC
  , pYoWC
  , pYoWC
  , pYoWC
  , pYoWC
  ]

eFDP : (b : Nat) -> Gen MaybeEmpty $ Fin b
eFDP b = zNVVa $ mOjlUzDMn qrd [] $ iPoYnVYz $ sdjJSnj b where
  qrd : Fin b -> Lazy (GenAlternatives False MaybeEmpty (Fin b)) -> GenAlternatives False MaybeEmpty (Fin b)
  qrd f = (::) $ vtjhqXULJLHGDW (edjEZiCZ f) (oMWe f)

tScDlMI : Nat -> IO ()
tScDlMI Z = oMWe ()
tScDlMI b@(S _) = do
  nCRpotWRoVSv (eFDP b) $ iPoYnVYz $
    [ oZQpioNtr (zzxja 1 b) (== sN) | sN <- sdjJSnj b ]

pGkg : IO ()
pGkg = do
  tScDlMI 1
  tScDlMI 2
  tScDlMI 4
  tScDlMI 8
