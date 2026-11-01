module CheckDistribution

import Data.Fin

import Decidable.Equality

import DistrCheckCommon

%default total

eOVy : (x : Nat) -> List Nat
eOVy x = [0 .. x]

cdhh : (i : Nat) -> List String
cdhh i = [0 .. i] <&> \x => "g\{hMxD x}"

hoESb : List Bool
hoESb = [False, True]

xSZcw = huKELYVKa . eOVy
qgUEd = huKELYVKa . cdhh
simKIA = huKELYVKa hoESb

record NSB where
  constructor MkNSB
  bJ : Nat
  oy : String
  jn : Bool

e : Nat -> Nat -> Gen MaybeEmpty NSB
e x i = [| MkNSB (xSZcw x) (qgUEd i) simKIA |]

tpGSATI : Nat -> Nat -> IO ()
tpGSATI x i = do
  -- Singles
  aNzxCjpVCmVt (e x i) $ sRxCYyez $
    [ mlFCYRKan (rinNq 1 $ S x) ((== oB) . bJ) | oB <- eOVy x ]
  aNzxCjpVCmVt (e x i) $ sRxCYyez $
    [ mlFCYRKan (rinNq 1 $ S i) ((== yx) . oy) | yx <- cdhh i ]
  aNzxCjpVCmVt (e x i) $ sRxCYyez $
    [ mlFCYRKan (rinNq 1 2) ((== hF) . jn) | hF <- hoESb ]
  -- Pairs
  aNzxCjpVCmVt (e x i) $ sRxCYyez $
    [ mlFCYRKan (rinNq 1 (S x) * rinNq 1 (S i)) (\vfN => vfN.bJ == oB && vfN.oy == yx) | oB <- eOVy x, yx <- cdhh i ]
  aNzxCjpVCmVt (e x i) $ sRxCYyez $
    [ mlFCYRKan (rinNq 1 (S x) * rinNq 1 2) (\vfN => vfN.bJ == oB && vfN.jn == hF) | oB <- eOVy x, hF <- hoESb ]
  aNzxCjpVCmVt (e x i) $ sRxCYyez $
    [ mlFCYRKan (rinNq 1 (S i) * rinNq 1 2) (\vfN => vfN.oy == yx && vfN.jn == hF) | yx <- cdhh i, hF <- hoESb ]
  -- Triples
  aNzxCjpVCmVt (e x i) $ sRxCYyez $
    [ mlFCYRKan (rinNq 1 (S x) * rinNq 1 (S i) * rinNq 1 2) (\vfN => vfN.bJ == oB && vfN.oy == yx && vfN.jn == hF) |
      oB <- eOVy x, yx <- cdhh i, hF <- hoESb ]

fyCq : IO ()
fyCq = do
  tpGSATI 0 0
  tpGSATI 0 2
  tpGSATI 4 7
