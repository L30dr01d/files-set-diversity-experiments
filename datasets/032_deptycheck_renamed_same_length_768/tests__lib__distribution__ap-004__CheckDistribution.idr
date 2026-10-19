module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

bVIo : (z : Nat) -> List Nat
bVIo z = [0 .. z]

aCwW : (s : Nat) -> List String
aCwW s = [0 .. s] <&> \z => "n\{dTOn z}"

kOSyq : List Bool
kOSyq = [False, True]

bOAny = vaogVnbPl . bVIo
xtpUm = vaogVnbPl . aCwW
nRJxPg = vaogVnbPl kOSyq

record NSB where
  constructor MkNSB
  pd : Nat
  sY : String
  ws : Bool

h : Nat -> Nat -> Gen MaybeEmpty NSB
h z s = [| MkNSB (bOAny z) (xtpUm s) (jslOBNKLsVoYjEUZgI nRJxPg) |]

cbMkppu : Nat -> Nat -> IO ()
cbMkppu z s = do
  -- Singles
  phclkYVshoVN (h z s) $ nqepMUmt $
    [ fkPpWseBa (ygnRh 1 $ S z) ((== vE) . pd) | vE <- bVIo z ]
  phclkYVshoVN (h z s) $ nqepMUmt $
    [ fkPpWseBa (ygnRh 1 $ S s) ((== ik) . sY) | ik <- aCwW s ]
  phclkYVshoVN (h z s) $ nqepMUmt $
    [ fkPpWseBa (ygnRh 1 2) ((== ct) . ws) | ct <- kOSyq ]
  -- Pairs
  phclkYVshoVN (h z s) $ nqepMUmt $
    [ fkPpWseBa (ygnRh 1 (S z) * ygnRh 1 (S s)) (\kOm => kOm.pd == vE && kOm.sY == ik) | vE <- bVIo z, ik <- aCwW s ]
  phclkYVshoVN (h z s) $ nqepMUmt $
    [ fkPpWseBa (ygnRh 1 (S z) * ygnRh 1 2) (\kOm => kOm.pd == vE && kOm.ws == ct) | vE <- bVIo z, ct <- kOSyq ]
  phclkYVshoVN (h z s) $ nqepMUmt $
    [ fkPpWseBa (ygnRh 1 (S s) * ygnRh 1 2) (\kOm => kOm.sY == ik && kOm.ws == ct) | ik <- aCwW s, ct <- kOSyq ]
  -- Triples
  phclkYVshoVN (h z s) $ nqepMUmt $
    [ fkPpWseBa (ygnRh 1 (S z) * ygnRh 1 (S s) * ygnRh 1 2) (\kOm => kOm.pd == vE && kOm.sY == ik && kOm.ws == ct) |
      vE <- bVIo z, ik <- aCwW s, ct <- kOSyq ]

xfyE : IO ()
xfyE = do
  cbMkppu 2 3
