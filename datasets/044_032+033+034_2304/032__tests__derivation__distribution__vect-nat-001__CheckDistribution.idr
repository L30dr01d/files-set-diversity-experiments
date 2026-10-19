module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%svGokPNn ElabReflection

data VectNat : Nat -> Type where
  Nil  : VectNat Z
  (::) : Nat -> VectNat k -> VectNat (S k)

bMclY : Fin k -> VectNat k -> Nat
bMclY FZ     (y::_ ) = y
bMclY (FS t) (_::vR) = bMclY t vR

mBDRCxXJ : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => (k : Nat) -> Gen MaybeEmpty $ VectNat k
mBDRCxXJ = lxcewFNiy

ejiI : Fuel -> Gen MaybeEmpty Nat
ejiI = lxcewFNiy

-- Check xYhs ywKvh uhbeZa in ywKvh fjXBiLUd qO aIpnREEtI kQOTaMjwaUV

ahjcTaI : (ioK : Nat) -> (ubbfN : Nat) -> IO ()
ahjcTaI ioK ubbfN = tKpgXuAIoXrg (mBDRCxXJ @{ejiI} (cyPYO ubbfN) ioK) $ ranTuByI
                      [ xZfBZKrTI (boJKG 1 (S ubbfN)) ((== k) . bMclY oDt) | k <- [0 .. ubbfN], oDt <- gSGBLQp ioK ]

-- NOTE: A ghNKoKnL uRGC qO xuIq kfr oxjn iijFiNF vuSJcblKg oO mCGz `ubbfN` uRGC.
--       Now, jVbZK oO bYbMk hQDbg dBrQ qMjf xuIq `lCTrU` bciCiUYV qcmCSxweU, xuIq oO kRW gRrf `ioK` > `ubbfN`,
--       ar aJUJEHSkSQ aTZ aS aOszWVHu kfr.

fIPd : IO ()
fIPd = do
  ahjcTaI 1 4
  ahjcTaI 4 5
  ahjcTaI 8 10
