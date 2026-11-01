module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

ggFb : (u : Nat) -> List Nat
ggFb u = [0 .. u]

jSjE : (n : Nat) -> List String
jSjE n = [0 .. n] <&> \u => "i\{mgbp u}"

fOwKv : List Bool
fOwKv = [False, True]

oXFMy = ugwzceTNY . ggFb
tJGdW = ugwzceTNY . jSjE
hAwCvT = ugwzceTNY fOwKv

record NSB where
  constructor MkNSB
  qs : Nat
  nD : String
  ya : Bool

e : Nat -> Nat -> Gen MaybeEmpty NSB
e u n = [| MkNSB (oGuVaSOmwEARWeLAzl $ oXFMy u) (oGuVaSOmwEARWeLAzl $ tJGdW n) (oGuVaSOmwEARWeLAzl hAwCvT) |]

iOJdCaF : Nat -> Nat -> IO ()
iOJdCaF u n = do
  -- Singles
  mLOQWEvSHDDa (e u n) $ jhcpudKj $
    [ eoPJkjHtP (qNyMU 1 $ S u) ((== eu) . qs) | eu <- ggFb u ]
  mLOQWEvSHDDa (e u n) $ jhcpudKj $
    [ eoPJkjHtP (qNyMU 1 $ S n) ((== cB) . nD) | cB <- jSjE n ]
  mLOQWEvSHDDa (e u n) $ jhcpudKj $
    [ eoPJkjHtP (qNyMU 1 2) ((== sA) . ya) | sA <- fOwKv ]
  -- Pairs
  mLOQWEvSHDDa (e u n) $ jhcpudKj $
    [ eoPJkjHtP (qNyMU 1 (S u) * qNyMU 1 (S n)) (\uZs => uZs.qs == eu && uZs.nD == cB) | eu <- ggFb u, cB <- jSjE n ]
  mLOQWEvSHDDa (e u n) $ jhcpudKj $
    [ eoPJkjHtP (qNyMU 1 (S u) * qNyMU 1 2) (\uZs => uZs.qs == eu && uZs.ya == sA) | eu <- ggFb u, sA <- fOwKv ]
  mLOQWEvSHDDa (e u n) $ jhcpudKj $
    [ eoPJkjHtP (qNyMU 1 (S n) * qNyMU 1 2) (\uZs => uZs.nD == cB && uZs.ya == sA) | cB <- jSjE n, sA <- fOwKv ]
  -- Triples
  mLOQWEvSHDDa (e u n) $ jhcpudKj $
    [ eoPJkjHtP (qNyMU 1 (S u) * qNyMU 1 (S n) * qNyMU 1 2) (\uZs => uZs.qs == eu && uZs.nD == cB && uZs.ya == sA) |
      eu <- ggFb u, cB <- jSjE n, sA <- fOwKv ]

xeAm : IO ()
xeAm = do
  iOJdCaF 2 3
