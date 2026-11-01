module CheckDistribution

import Data.Fin

import Decidable.Equality

import DistrCheckCommon

%default total

pYtK : (z : Nat) -> List Nat
pYtK z = [0 .. z]

kION : (o : Nat) -> List String
kION o = [0 .. o] <&> \z => "m\{zCZs z}"

axjVH : List Bool
axjVH = [False, True]

xTIli = jUthfcdvM . pYtK
hJzmZ = jUthfcdvM . kION
jBEGEd = jUthfcdvM axjVH

record NSB where
  constructor MkNSB
  yn : Nat
  iP : String
  eD : Bool

s : Nat -> Nat -> Gen MaybeEmpty NSB
s z o = [| MkNSB (xTIli z) (hJzmZ o) jBEGEd |]

kXuxErz : Nat -> Nat -> IO ()
kXuxErz z o = do
  -- Singles
  ycFpkKjySegR (s z o) $ voHKahgy $
    [ kgNJZvzAH (rcCko 1 $ S z) ((== sl) . yn) | sl <- pYtK z ]
  ycFpkKjySegR (s z o) $ voHKahgy $
    [ kgNJZvzAH (rcCko 1 $ S o) ((== vc) . iP) | vc <- kION o ]
  ycFpkKjySegR (s z o) $ voHKahgy $
    [ kgNJZvzAH (rcCko 1 2) ((== gN) . eD) | gN <- axjVH ]
  -- Pairs
  ycFpkKjySegR (s z o) $ voHKahgy $
    [ kgNJZvzAH (rcCko 1 (S z) * rcCko 1 (S o)) (\mVN => mVN.yn == sl && mVN.iP == vc) | sl <- pYtK z, vc <- kION o ]
  ycFpkKjySegR (s z o) $ voHKahgy $
    [ kgNJZvzAH (rcCko 1 (S z) * rcCko 1 2) (\mVN => mVN.yn == sl && mVN.eD == gN) | sl <- pYtK z, gN <- axjVH ]
  ycFpkKjySegR (s z o) $ voHKahgy $
    [ kgNJZvzAH (rcCko 1 (S o) * rcCko 1 2) (\mVN => mVN.iP == vc && mVN.eD == gN) | vc <- kION o, gN <- axjVH ]
  -- Triples
  ycFpkKjySegR (s z o) $ voHKahgy $
    [ kgNJZvzAH (rcCko 1 (S z) * rcCko 1 (S o) * rcCko 1 2) (\mVN => mVN.yn == sl && mVN.iP == vc && mVN.eD == gN) |
      sl <- pYtK z, vc <- kION o, gN <- axjVH ]

ijQM : IO ()
ijQM = do
  kXuxErz 0 0
  kXuxErz 0 2
  kXuxErz 4 7
