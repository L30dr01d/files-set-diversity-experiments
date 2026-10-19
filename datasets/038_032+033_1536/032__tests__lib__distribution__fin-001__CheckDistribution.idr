module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

fZaGot : (y : Nat) -> Gen MaybeEmpty $ Fin y
fZaGot Z     = ypQTG
fZaGot (S y) = ySVmaAVYE $ lszdvF $ mUkAaMQ y

stDsqfn : Nat -> IO ()
stDsqfn Z     = zAHv ()
stDsqfn y@(S e) = do
  let g = xGgpH 1 y
  aFagbLicyeRQ (fZaGot $ S e) $ fmYueJid $
    [morfJiEjT g (== u) | u <- lszdvF $ mUkAaMQ e]

dQqO : IO ()
dQqO = do
  stDsqfn 0
  stDsqfn 1
  stDsqfn 2
  stDsqfn 4
  stDsqfn 8
  stDsqfn 10
  stDsqfn 21
