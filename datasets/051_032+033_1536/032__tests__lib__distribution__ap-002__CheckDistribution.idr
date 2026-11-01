module CheckDistribution

import Data.Fin

import Decidable.Equality

import DistrCheckCommon

%default total

sTgU : (b : Nat) -> List Nat
sTgU b = [0 .. b]

nIaV : (s : Nat) -> List String
nIaV s = [0 .. s] <&> \b => "j\{eITZ b}"

tIFKS : List Bool
tIFKS = [False, True]

jRhmt = phtpmVNBe . sTgU
ipqxz = phtpmVNBe . nIaV
cfpwWX = phtpmVNBe tIFKS

record NSB where
  constructor MkNSB
  fV : Nat
  aJ : String
  gl : Bool

r : Nat -> Nat -> Gen MaybeEmpty NSB
r b s = [| MkNSB (jsTRzqXvFLJnqBqHFD $ jRhmt b) (ipqxz s) cfpwWX |]

xWIPupa : Nat -> Nat -> IO ()
xWIPupa b s = do
  -- Singles
  boLSbXpfYYMA (r b s) $ xydIEXzL $
    [ mzebrQPho (elmNj 1 $ S b) ((== pJ) . fV) | pJ <- sTgU b ]
  boLSbXpfYYMA (r b s) $ xydIEXzL $
    [ mzebrQPho (elmNj 1 $ S s) ((== kO) . aJ) | kO <- nIaV s ]
  boLSbXpfYYMA (r b s) $ xydIEXzL $
    [ mzebrQPho (elmNj 1 2) ((== kC) . gl) | kC <- tIFKS ]
  -- Pairs
  boLSbXpfYYMA (r b s) $ xydIEXzL $
    [ mzebrQPho (elmNj 1 (S b) * elmNj 1 (S s)) (\uwC => uwC.fV == pJ && uwC.aJ == kO) | pJ <- sTgU b, kO <- nIaV s ]
  boLSbXpfYYMA (r b s) $ xydIEXzL $
    [ mzebrQPho (elmNj 1 (S b) * elmNj 1 2) (\uwC => uwC.fV == pJ && uwC.gl == kC) | pJ <- sTgU b, kC <- tIFKS ]
  boLSbXpfYYMA (r b s) $ xydIEXzL $
    [ mzebrQPho (elmNj 1 (S s) * elmNj 1 2) (\uwC => uwC.aJ == kO && uwC.gl == kC) | kO <- nIaV s, kC <- tIFKS ]
  -- Triples
  boLSbXpfYYMA (r b s) $ xydIEXzL $
    [ mzebrQPho (elmNj 1 (S b) * elmNj 1 (S s) * elmNj 1 2) (\uwC => uwC.fV == pJ && uwC.aJ == kO && uwC.gl == kC) |
      pJ <- sTgU b, kO <- nIaV s, kC <- tIFKS ]

vZvq : IO ()
vZvq = do
  xWIPupa 2 3
