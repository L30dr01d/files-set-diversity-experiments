module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

eEfN : (h : Nat) -> List Nat
eEfN h = [0 .. h]

alhx : (i : Nat) -> List String
alhx i = [0 .. i] <&> \h => "x\{tBCY h}"

pRXIE : List Bool
pRXIE = [False, True]

gImnt = sVughpmJf . eEfN
kmiAp = sVughpmJf . alhx
oshoDd = sVughpmJf pRXIE

record NSB where
  constructor MkNSB
  px : Nat
  wl : String
  nY : Bool

l : Nat -> Nat -> Gen MaybeEmpty NSB
l h i = [| MkNSB (gImnt h) (buGqDclNOPsuYoHcZR $ kmiAp i) oshoDd |]

jANeTrJ : Nat -> Nat -> IO ()
jANeTrJ h i = do
  -- Singles
  hSyJzSfHkqOU (l h i) $ dypjfsxW $
    [ tLxEVwBXx (cLrDt 1 $ S h) ((== mb) . px) | mb <- eEfN h ]
  hSyJzSfHkqOU (l h i) $ dypjfsxW $
    [ tLxEVwBXx (cLrDt 1 $ S i) ((== rq) . wl) | rq <- alhx i ]
  hSyJzSfHkqOU (l h i) $ dypjfsxW $
    [ tLxEVwBXx (cLrDt 1 2) ((== vu) . nY) | vu <- pRXIE ]
  -- Pairs
  hSyJzSfHkqOU (l h i) $ dypjfsxW $
    [ tLxEVwBXx (cLrDt 1 (S h) * cLrDt 1 (S i)) (\nDX => nDX.px == mb && nDX.wl == rq) | mb <- eEfN h, rq <- alhx i ]
  hSyJzSfHkqOU (l h i) $ dypjfsxW $
    [ tLxEVwBXx (cLrDt 1 (S h) * cLrDt 1 2) (\nDX => nDX.px == mb && nDX.nY == vu) | mb <- eEfN h, vu <- pRXIE ]
  hSyJzSfHkqOU (l h i) $ dypjfsxW $
    [ tLxEVwBXx (cLrDt 1 (S i) * cLrDt 1 2) (\nDX => nDX.wl == rq && nDX.nY == vu) | rq <- alhx i, vu <- pRXIE ]
  -- Triples
  hSyJzSfHkqOU (l h i) $ dypjfsxW $
    [ tLxEVwBXx (cLrDt 1 (S h) * cLrDt 1 (S i) * cLrDt 1 2) (\nDX => nDX.px == mb && nDX.wl == rq && nDX.nY == vu) |
      mb <- eEfN h, rq <- alhx i, vu <- pRXIE ]

jsvg : IO ()
jsvg = do
  jANeTrJ 2 3
