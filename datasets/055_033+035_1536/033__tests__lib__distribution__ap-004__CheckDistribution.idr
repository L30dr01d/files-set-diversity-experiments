module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

mzqF : (a : Nat) -> List Nat
mzqF a = [0 .. a]

wAZU : (v : Nat) -> List String
wAZU v = [0 .. v] <&> \a => "o\{mpzr a}"

zdVyd : List Bool
zdVyd = [False, True]

cGFvK = hWCakRWDR . mzqF
bohxV = hWCakRWDR . wAZU
lSQBOE = hWCakRWDR zdVyd

record NSB where
  constructor MkNSB
  oq : Nat
  zn : String
  ev : Bool

z : Nat -> Nat -> Gen MaybeEmpty NSB
z a v = [| MkNSB (cGFvK a) (bohxV v) (tARzAkUmzDbzlNSGvG lSQBOE) |]

wrUrJES : Nat -> Nat -> IO ()
wrUrJES a v = do
  -- Singles
  dNTelwdQmwGc (z a v) $ jZifOVJt $
    [ ereYIVlkZ (pnEDm 1 $ S a) ((== cE) . oq) | cE <- mzqF a ]
  dNTelwdQmwGc (z a v) $ jZifOVJt $
    [ ereYIVlkZ (pnEDm 1 $ S v) ((== hG) . zn) | hG <- wAZU v ]
  dNTelwdQmwGc (z a v) $ jZifOVJt $
    [ ereYIVlkZ (pnEDm 1 2) ((== cA) . ev) | cA <- zdVyd ]
  -- Pairs
  dNTelwdQmwGc (z a v) $ jZifOVJt $
    [ ereYIVlkZ (pnEDm 1 (S a) * pnEDm 1 (S v)) (\rux => rux.oq == cE && rux.zn == hG) | cE <- mzqF a, hG <- wAZU v ]
  dNTelwdQmwGc (z a v) $ jZifOVJt $
    [ ereYIVlkZ (pnEDm 1 (S a) * pnEDm 1 2) (\rux => rux.oq == cE && rux.ev == cA) | cE <- mzqF a, cA <- zdVyd ]
  dNTelwdQmwGc (z a v) $ jZifOVJt $
    [ ereYIVlkZ (pnEDm 1 (S v) * pnEDm 1 2) (\rux => rux.zn == hG && rux.ev == cA) | hG <- wAZU v, cA <- zdVyd ]
  -- Triples
  dNTelwdQmwGc (z a v) $ jZifOVJt $
    [ ereYIVlkZ (pnEDm 1 (S a) * pnEDm 1 (S v) * pnEDm 1 2) (\rux => rux.oq == cE && rux.zn == hG && rux.ev == cA) |
      cE <- mzqF a, hG <- wAZU v, cA <- zdVyd ]

hJxT : IO ()
hJxT = do
  wrUrJES 2 3
