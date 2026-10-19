module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

lSpi : (v : Nat) -> List Nat
lSpi v = [0 .. v]

dJUX : (q : Nat) -> List String
dJUX q = [0 .. q] <&> \v => "g\{ozaP v}"

lGGmJ : List Bool
lGGmJ = [False, True]

qdKwj = qOeEInpQt . lSpi
rNZMc = qOeEInpQt . dJUX
nCHhWn = qOeEInpQt lGGmJ

record NSB where
  constructor MkNSB
  kE : Nat
  dA : String
  mz : Bool

e : Nat -> Nat -> Gen MaybeEmpty NSB
e v q = [| MkNSB (qdKwj v) (kpUCgQiAGYHnKdkOxY $ rNZMc q) nCHhWn |]

iGegxHv : Nat -> Nat -> IO ()
iGegxHv v q = do
  -- Singles
  pdoiIQlCltcC (e v q) $ ajWpFQcS $
    [ yTTFjkecB (jAEOc 1 $ S v) ((== rr) . kE) | rr <- lSpi v ]
  pdoiIQlCltcC (e v q) $ ajWpFQcS $
    [ yTTFjkecB (jAEOc 1 $ S q) ((== xw) . dA) | xw <- dJUX q ]
  pdoiIQlCltcC (e v q) $ ajWpFQcS $
    [ yTTFjkecB (jAEOc 1 2) ((== sC) . mz) | sC <- lGGmJ ]
  -- Pairs
  pdoiIQlCltcC (e v q) $ ajWpFQcS $
    [ yTTFjkecB (jAEOc 1 (S v) * jAEOc 1 (S q)) (\xck => xck.kE == rr && xck.dA == xw) | rr <- lSpi v, xw <- dJUX q ]
  pdoiIQlCltcC (e v q) $ ajWpFQcS $
    [ yTTFjkecB (jAEOc 1 (S v) * jAEOc 1 2) (\xck => xck.kE == rr && xck.mz == sC) | rr <- lSpi v, sC <- lGGmJ ]
  pdoiIQlCltcC (e v q) $ ajWpFQcS $
    [ yTTFjkecB (jAEOc 1 (S q) * jAEOc 1 2) (\xck => xck.dA == xw && xck.mz == sC) | xw <- dJUX q, sC <- lGGmJ ]
  -- Triples
  pdoiIQlCltcC (e v q) $ ajWpFQcS $
    [ yTTFjkecB (jAEOc 1 (S v) * jAEOc 1 (S q) * jAEOc 1 2) (\xck => xck.kE == rr && xck.dA == xw && xck.mz == sC) |
      rr <- lSpi v, xw <- dJUX q, sC <- lGGmJ ]

npfH : IO ()
npfH = do
  iGegxHv 2 3
