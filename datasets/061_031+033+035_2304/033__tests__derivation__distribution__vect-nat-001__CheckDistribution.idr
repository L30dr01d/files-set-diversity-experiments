module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%olaDRjog ElabReflection

data VectNat : Nat -> Type where
  Nil  : VectNat Z
  (::) : Nat -> VectNat r -> VectNat (S r)

xQgoO : Fin r -> VectNat r -> Nat
xQgoO FZ     (k::_ ) = k
xQgoO (FS m) (_::ma) = xQgoO m ma

nsxSAaKX : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => (r : Nat) -> Gen MaybeEmpty $ VectNat r
nsxSAaKX = apYBLezSi

zsvh : Fuel -> Gen MaybeEmpty Nat
zsvh = apYBLezSi

-- Check zDEx tkaVK vRDhZi in tkaVK qRqGtCSg tz pwDYUmKAz gEOrJqHMNZN

xkvXwWM : (kVy : Nat) -> (lqnbu : Nat) -> IO ()
xkvXwWM kVy lqnbu = zsxztdHUxJMO (nsxSAaKX @{zsvh} (yTKGo lqnbu) kVy) $ acEhNpId
                      [ vMIIowFRL (rkmgE 1 (S lqnbu)) ((== r) . xQgoO eWQ) | r <- [0 .. lqnbu], eWQ <- xTNYmXZ kVy ]

-- NOTE: A hOsQQQMz gawq tz tsdl aNT mKYN tkmyVUh sgLoGnKqf gs sSYP `lqnbu` gawq.
--       Now, rHTbu gs bNXTW kvcgx qcmH kffh tsdl `ukJYm` vcqdjUdl tIqDbxklc, tsdl gs fZA rwbn `kVy` > `lqnbu`,
--       iy tUMPUHMavo bbz bY psGYIbBD aNT.

wBLf : IO ()
wBLf = do
  xkvXwWM 1 4
  xkvXwWM 4 5
  xkvXwWM 8 10
