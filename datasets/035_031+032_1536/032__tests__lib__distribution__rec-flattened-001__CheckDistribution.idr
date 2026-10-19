module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

dSIb : Gen MaybeEmpty Nat
dSIb = jfjeHmXv [0 .. 9]

rhjSQ : (uCosKv : Nat) -> Gen MaybeEmpty l -> Gen MaybeEmpty $ List l
rhjSQ Z     _  = oXWp []
rhjSQ (S s) as = ppQjs
  $  [| [] |]
  :: [| [as] :: lODurOMXRHYVFS (rhjSQ s as) |]

cLEIrJX : (uCosKv : Nat) -> IO ()
cLEIrJX uCosKv = tNdTmElXfGMs (rhjSQ uCosKv dSIb) $ vzrC (S uCosKv) [0, 1 ..] <&> \q => psJAyVuAp (azERj 1 (S uCosKv)) ((== q) . tlqEVV)

loCg : IO ()
loCg = do
  cLEIrJX 0
  cLEIrJX 1
  cLEIrJX 2
  cLEIrJX 10
  cLEIrJX 20
