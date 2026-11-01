module CheckDistribution

import Data.Fin

import Decidable.Equality

import DistrCheckCommon

%default total

mAnI : (w : Nat) -> List Nat
mAnI w = [0 .. w]

cbsV : (y : Nat) -> List String
cbsV y = [0 .. y] <&> \w => "d\{ykxk w}"

ysYRH : List Bool
ysYRH = [False, True]

lLfjj = qkXsckDai . mAnI
kzaLt = qkXsckDai . cbsV
iYnKAS = qkXsckDai ysYRH

record NSB where
  constructor MkNSB
  hA : Nat
  aB : String
  oz : Bool

m : Nat -> Nat -> Gen MaybeEmpty NSB
m w y = [| MkNSB (kyOPVlasTsbYwxhoCY $ lLfjj w) (kzaLt y) iYnKAS |]

sOngwKD : Nat -> Nat -> IO ()
sOngwKD w y = do
  -- Singles
  emrndvFEMGJP (m w y) $ rCRoWwIq $
    [ byOzfOCDQ (lAyZN 1 $ S w) ((== dO) . hA) | dO <- mAnI w ]
  emrndvFEMGJP (m w y) $ rCRoWwIq $
    [ byOzfOCDQ (lAyZN 1 $ S y) ((== bd) . aB) | bd <- cbsV y ]
  emrndvFEMGJP (m w y) $ rCRoWwIq $
    [ byOzfOCDQ (lAyZN 1 2) ((== tw) . oz) | tw <- ysYRH ]
  -- Pairs
  emrndvFEMGJP (m w y) $ rCRoWwIq $
    [ byOzfOCDQ (lAyZN 1 (S w) * lAyZN 1 (S y)) (\hCL => hCL.hA == dO && hCL.aB == bd) | dO <- mAnI w, bd <- cbsV y ]
  emrndvFEMGJP (m w y) $ rCRoWwIq $
    [ byOzfOCDQ (lAyZN 1 (S w) * lAyZN 1 2) (\hCL => hCL.hA == dO && hCL.oz == tw) | dO <- mAnI w, tw <- ysYRH ]
  emrndvFEMGJP (m w y) $ rCRoWwIq $
    [ byOzfOCDQ (lAyZN 1 (S y) * lAyZN 1 2) (\hCL => hCL.aB == bd && hCL.oz == tw) | bd <- cbsV y, tw <- ysYRH ]
  -- Triples
  emrndvFEMGJP (m w y) $ rCRoWwIq $
    [ byOzfOCDQ (lAyZN 1 (S w) * lAyZN 1 (S y) * lAyZN 1 2) (\hCL => hCL.hA == dO && hCL.aB == bd && hCL.oz == tw) |
      dO <- mAnI w, bd <- cbsV y, tw <- ysYRH ]

eDTk : IO ()
eDTk = do
  sOngwKD 2 3
